// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Union-find liveness (DR-CHC-DPE-UNION-FIND-20261118): differential check
//! against the replaced clique-edge algorithm, the depth cut-off it had, its
//! scaling, and the stop contract.

use super::*;
use crate::{ChcOp, ClauseBody, ClauseHead, HornClause};
use ay_core::kani_compat::{DetHashMap as RefMap, DetHashSet as RefSet};
use std::sync::Arc;

/// The REPLACED algorithm, kept verbatim in behaviour as the oracle: per
/// clause, seed non-variable arguments, constraint variables (plus the
/// solved-equality pass) and body joins; link every pair of positions that
/// share a variable; close with a worklist. Variables come from
/// `ChcExpr::vars()`, which stops at `MAX_EXPR_RECURSION_DEPTH`.
mod reference {
    use super::*;

    type Key = (PredicateId, usize);

    struct Position {
        key: Key,
        is_var: bool,
        vars: RefSet<ChcVar>,
        body: bool,
    }

    fn solved_equality(expr: &ChcExpr) -> Option<(ChcVar, Vec<ChcVar>)> {
        match expr {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(var), rhs) | (rhs, ChcExpr::Var(var)) => {
                        let vars = rhs.vars();
                        (!vars.is_empty()).then(|| (var.clone(), vars))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    pub(super) fn live(problem: &ChcProblem) -> RefMap<PredicateId, RefSet<usize>> {
        let mut live: RefMap<PredicateId, RefSet<usize>> = problem
            .predicates()
            .iter()
            .map(|pred| (pred.id, RefSet::default()))
            .collect();
        let mark = |live: &mut RefMap<PredicateId, RefSet<usize>>, key: Key| {
            if let Some(set) = live.get_mut(&key.0) {
                set.insert(key.1);
            }
        };
        let mut edges: RefMap<Key, RefSet<Key>> = RefMap::default();
        for clause in problem.clauses() {
            let mut positions = Vec::new();
            for (pred, args) in &clause.body.predicates {
                for (pos, arg) in args.iter().enumerate() {
                    positions.push(Position {
                        key: (*pred, pos),
                        is_var: matches!(arg, ChcExpr::Var(_)),
                        vars: arg.vars().into_iter().collect(),
                        body: true,
                    });
                }
            }
            if let ClauseHead::Predicate(pred, args) = &clause.head {
                for (pos, arg) in args.iter().enumerate() {
                    positions.push(Position {
                        key: (*pred, pos),
                        is_var: matches!(arg, ChcExpr::Var(_)),
                        vars: arg.vars().into_iter().collect(),
                        body: false,
                    });
                }
            }
            for position in &positions {
                if !position.is_var {
                    mark(&mut live, position.key);
                }
            }
            if let Some(constraint) = clause.body.constraint.as_ref() {
                let mut seeds: RefSet<ChcVar> = constraint.vars().into_iter().collect();
                for conjunct in constraint.collect_conjuncts() {
                    if let Some((var, vars)) = solved_equality(&conjunct) {
                        seeds.insert(var);
                        seeds.extend(vars);
                    }
                }
                for position in &positions {
                    if position.vars.iter().any(|var| seeds.contains(var)) {
                        mark(&mut live, position.key);
                    }
                }
            }
            let mut body_vars: RefMap<ChcVar, RefSet<Key>> = RefMap::default();
            for position in positions.iter().filter(|position| position.body) {
                for var in &position.vars {
                    body_vars
                        .entry(var.clone())
                        .or_default()
                        .insert(position.key);
                }
            }
            for keys in body_vars.values() {
                if keys.len() > 1 {
                    for &key in keys {
                        mark(&mut live, key);
                    }
                }
            }
            for (index, lhs) in positions.iter().enumerate() {
                for rhs in &positions[index + 1..] {
                    if lhs.vars.iter().any(|var| rhs.vars.contains(var)) {
                        edges.entry(lhs.key).or_default().insert(rhs.key);
                        edges.entry(rhs.key).or_default().insert(lhs.key);
                    }
                }
            }
        }
        let mut reached: RefSet<Key> = RefSet::default();
        let mut worklist = Vec::new();
        for &key in edges.keys() {
            if live.get(&key.0).is_some_and(|set| set.contains(&key.1)) && reached.insert(key) {
                worklist.push(key);
            }
        }
        while let Some(key) = worklist.pop() {
            for &next in edges.get(&key).into_iter().flatten() {
                if reached.insert(next) {
                    worklist.push(next);
                }
            }
        }
        for key in reached {
            mark(&mut live, key);
        }
        live
    }
}

fn int_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

fn op(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}

/// `(ite (< w k) ... (ite (< w 1) (ite (< w 0) bottom w) w) ... w)`, nested
/// `depth` times. The guards read the local `w`, which no argument mentions,
/// so constant folding (`add_clause` simplifies constraints) cannot collapse
/// the chain; callers still check the depth that survived.
fn deep_over(bottom: ChcExpr, depth: usize) -> ChcExpr {
    let w = ChcExpr::Var(int_var("w"));
    (0..depth).fold(bottom, |inner, k| {
        op(
            ChcOp::Ite,
            vec![
                op(ChcOp::Lt, vec![w.clone(), ChcExpr::Int(k as i128)]),
                inner,
                w.clone(),
            ],
        )
    })
}

/// Whether `expr` really is deeper than the replaced walk's cut-off.
fn beyond_cutoff(expr: &ChcExpr) -> bool {
    crate::expr::dag::longest_path_at_least(expr, 500)
}

fn live_vector(problem: &ChcProblem, live: &analysis::LivePositions) -> Vec<Vec<bool>> {
    problem
        .predicates()
        .iter()
        .map(|pred| {
            (0..pred.arity())
                .map(|pos| live.is_live(pred.id, pos))
                .collect()
        })
        .collect()
}

fn reference_vector(problem: &ChcProblem) -> Vec<Vec<bool>> {
    let live = reference::live(problem);
    problem
        .predicates()
        .iter()
        .map(|pred| {
            (0..pred.arity())
                .map(|pos| live[&pred.id].contains(&pos))
                .collect()
        })
        .collect()
}

/// xorshift64*: deterministic, dependency-free.
struct Rng(u64);

impl Rng {
    fn step(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.step() % n as u64) as usize
    }

    fn chance(&mut self, percent: usize) -> bool {
        self.below(100) < percent
    }
}

fn random_term(rng: &mut Rng, vars: &[ChcVar]) -> ChcExpr {
    let var = |rng: &mut Rng| ChcExpr::Var(vars[rng.below(vars.len())].clone());
    match rng.below(4) {
        0 => ChcExpr::Int(rng.below(3) as i128),
        1 => op(ChcOp::Add, vec![var(rng), ChcExpr::Int(1)]),
        2 => op(ChcOp::Add, vec![var(rng), var(rng)]),
        _ => op(ChcOp::Mul, vec![ChcExpr::Int(2), var(rng)]),
    }
}

/// Subterms one clause shares (same `Arc`) between several arguments, so the
/// per-clause walked-node skip is exercised. Later entries may contain
/// earlier ones.
fn random_shared(rng: &mut Rng, vars: &[ChcVar]) -> Vec<Arc<ChcExpr>> {
    let mut pool: Vec<Arc<ChcExpr>> = Vec::new();
    for _ in 0..rng.below(4) {
        let var = Arc::new(ChcExpr::Var(vars[rng.below(vars.len())].clone()));
        let then = if !pool.is_empty() && rng.chance(50) {
            pool[rng.below(pool.len())].clone()
        } else {
            Arc::new(random_term(rng, vars))
        };
        let guard = Arc::new(op(ChcOp::Lt, vec![(*var).clone(), ChcExpr::Int(0)]));
        pool.push(Arc::new(ChcExpr::Op(ChcOp::Ite, vec![guard, then, var])));
    }
    pool
}

fn random_arg(rng: &mut Rng, vars: &[ChcVar], shared: &[Arc<ChcExpr>]) -> ChcExpr {
    if rng.chance(65) {
        ChcExpr::Var(vars[rng.below(vars.len())].clone())
    } else if !shared.is_empty() && rng.chance(40) {
        ChcExpr::Op(
            ChcOp::Mul,
            vec![
                Arc::new(ChcExpr::Int(3)),
                shared[rng.below(shared.len())].clone(),
            ],
        )
    } else {
        random_term(rng, vars)
    }
}

fn random_atom(rng: &mut Rng, vars: &[ChcVar]) -> ChcExpr {
    let var = ChcExpr::Var(vars[rng.below(vars.len())].clone());
    match rng.below(3) {
        // Solved equality, both orientations (the deleted pass's input).
        0 => op(ChcOp::Eq, vec![var, random_term(rng, vars)]),
        1 => op(ChcOp::Eq, vec![random_term(rng, vars), var]),
        _ => op(ChcOp::Lt, vec![var, ChcExpr::Int(0)]),
    }
}

fn random_problem(rng: &mut Rng) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let preds: Vec<(PredicateId, usize)> = (0..=rng.below(4))
        .map(|index| {
            let arity = rng.below(5);
            let id = problem.declare_predicate(format!("P{index}"), vec![ChcSort::Int; arity]);
            (id, arity)
        })
        .collect();
    let vars: Vec<ChcVar> = (0..=rng.below(6))
        .map(|index| int_var(&format!("v{index}")))
        .collect();
    for _ in 0..=rng.below(5) {
        let shared = random_shared(rng, &vars);
        let body = (0..rng.below(4))
            .map(|_| {
                let (id, arity) = preds[rng.below(preds.len())];
                (
                    id,
                    (0..arity)
                        .map(|_| random_arg(rng, &vars, &shared))
                        .collect(),
                )
            })
            .collect();
        let constraint = match rng.below(4) {
            0 => None,
            1 => Some(random_atom(rng, &vars)),
            _ => Some(op(
                ChcOp::And,
                (0..=rng.below(3))
                    .map(|_| random_atom(rng, &vars))
                    .collect(),
            )),
        };
        let head = if rng.chance(30) {
            ClauseHead::False
        } else {
            let (id, arity) = preds[rng.below(preds.len())];
            ClauseHead::Predicate(
                id,
                (0..arity)
                    .map(|_| random_arg(rng, &vars, &shared))
                    .collect(),
            )
        };
        problem.add_clause(HornClause::new(ClauseBody::new(body, constraint), head));
    }
    problem
}

/// Whether two arguments of `clause` reach one inner node (same address).
fn shares_inner_node_across_arguments(clause: &HornClause) -> bool {
    let mut owner: RefMap<*const ChcExpr, usize> = RefMap::default();
    let head_args = match &clause.head {
        ClauseHead::Predicate(_, args) => args.as_slice(),
        ClauseHead::False => &[],
    };
    let args = clause
        .body
        .predicates
        .iter()
        .flat_map(|(_, args)| args.iter())
        .chain(head_args);
    let mut shared = false;
    for (index, arg) in args.enumerate() {
        crate::expr::dag::walk_distinct_preorder(arg, |node| {
            if crate::expr::dag::has_children(node) {
                let first = *owner.entry(std::ptr::from_ref(node)).or_insert(index);
                shared |= first != index;
            }
            crate::expr::dag::Step::Descend
        });
    }
    shared
}

#[test]
fn union_find_liveness_equals_the_replaced_clique_closure() {
    let eliminator = DeadParamEliminator::new();
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let mut eliminated = 0usize;
    let mut sharing_clauses = 0usize;
    for trial in 0..20_000 {
        let problem = random_problem(&mut rng);
        let expected = reference_vector(&problem);
        let actual = live_vector(&problem, &eliminator.compute_live_positions(&problem));
        assert_eq!(actual, expected, "trial {trial}: {problem:?}");
        eliminated += expected.iter().flatten().filter(|live| !**live).count();
        sharing_clauses += problem
            .clauses()
            .iter()
            .filter(|clause| shares_inner_node_across_arguments(clause))
            .count();
    }
    // The generator must exercise both answers, not only "all live", and
    // clauses whose arguments share inner nodes (the walked-node skip).
    assert!(eliminated > 1_000, "only {eliminated} dead positions");
    assert!(
        sharing_clauses > 1_000,
        "only {sharing_clauses} clauses share a node across arguments"
    );
}

/// `P(x, y) /\ deep(y) = 0 -> false` with `y` only below depth 500: the
/// replaced walk never saw `y` and dropped a position the query reads.
#[test]
fn constraint_deeper_than_the_cutoff_keeps_its_position_live() {
    let (x, y) = (int_var("x"), int_var("y"));
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            Vec::new(),
            Some(op(
                ChcOp::Eq,
                vec![ChcExpr::Var(x.clone()), ChcExpr::Int(0)],
            )),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::Var(x.clone()), ChcExpr::Var(y.clone())]),
    ));
    let deep = deep_over(ChcExpr::Var(y.clone()), 600);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::Var(x), ChcExpr::Var(y)])],
            Some(op(ChcOp::Eq, vec![deep, ChcExpr::Int(0)])),
        ),
        ClauseHead::False,
    ));
    let stored = problem.clauses()[1].body.constraint.as_ref().unwrap();
    assert!(beyond_cutoff(stored), "the constraint kept its depth");
    assert_eq!(
        reference_vector(&problem),
        vec![vec![true, false]],
        "the replaced walk misses y"
    );
    let live = DeadParamEliminator::new().compute_live_positions(&problem);
    assert_eq!(live_vector(&problem, &live), vec![vec![true, true]]);
    let (reduced, map) = DeadParamEliminator::new().eliminate(&problem);
    assert_eq!(reduced.predicates()[0].arity(), 2);
    assert!(map[&p].iter().all(Option::is_some));
}

/// `P(x, y) -> Q(deep(y))` with `y` only below depth 500 of the head
/// argument, and `Q(z) /\ z < 0 -> false`: the head position is seeded
/// (non-variable), and `y` links it to `P`'s second position.
#[test]
fn deep_head_argument_links_its_body_position() {
    let (x, y, z) = (int_var("x"), int_var("y"), int_var("z"));
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            Vec::new(),
            Some(op(
                ChcOp::Eq,
                vec![ChcExpr::Var(x.clone()), ChcExpr::Int(0)],
            )),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::Var(x.clone()), ChcExpr::Var(y.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::Var(x), ChcExpr::Var(y.clone())])],
            None,
        ),
        ClauseHead::Predicate(q, vec![deep_over(ChcExpr::Var(y), 600)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::Var(z.clone())])],
            Some(op(ChcOp::Lt, vec![ChcExpr::Var(z), ChcExpr::Int(0)])),
        ),
        ClauseHead::False,
    ));
    let ClauseHead::Predicate(_, head_args) = &problem.clauses()[1].head else {
        panic!("clause 1 has a predicate head");
    };
    assert!(
        beyond_cutoff(&head_args[0]),
        "the head argument kept its depth"
    );
    assert_eq!(
        reference_vector(&problem),
        vec![vec![true, false], vec![true]],
        "the replaced walk misses y"
    );
    let live = DeadParamEliminator::new().compute_live_positions(&problem);
    assert_eq!(
        live_vector(&problem, &live),
        vec![vec![true, true], vec![true]]
    );
}

/// One `arity`-ary predicate whose transition passes `arity - 1` arguments
/// through. Only position 0 is live.
fn wide_problem(arity: usize) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int; arity]);
    let xs: Vec<ChcVar> = (0..arity).map(|i| int_var(&format!("x{i}"))).collect();
    let args = |vars: &[ChcVar]| vars.iter().cloned().map(ChcExpr::Var).collect::<Vec<_>>();
    let x0 = ChcExpr::Var(xs[0].clone());
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            Vec::new(),
            Some(op(ChcOp::Eq, vec![x0.clone(), ChcExpr::Int(0)])),
        ),
        ClauseHead::Predicate(p, args(&xs)),
    ));
    let mut next = xs.clone();
    next[0] = int_var("x0_next");
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, args(&xs))],
            Some(op(
                ChcOp::Eq,
                vec![
                    ChcExpr::Var(next[0].clone()),
                    op(ChcOp::Add, vec![x0.clone(), ChcExpr::Int(1)]),
                ],
            )),
        ),
        ClauseHead::Predicate(p, args(&next)),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, args(&xs))],
            Some(op(ChcOp::Lt, vec![x0, ChcExpr::Int(0)])),
        ),
        ClauseHead::False,
    ));
    problem
}

/// At arity 65,536 the transition clause has 131,072 positions, which the
/// replaced all-pairs scan tested pairwise (~8.6 G tests; measured at arity
/// 4096 it already took 0.7-1.2 s at the dev profile, and the cost grows with
/// the square), so it cannot meet the timeout; the union-find is linear.
#[test]
#[ntest::timeout(10_000)]
fn large_arity_liveness_is_linear_in_positions() {
    let arity = 1 << 16;
    let problem = wide_problem(arity);
    let live = DeadParamEliminator::new().compute_live_positions(&problem);
    let mut expected = vec![false; arity];
    expected[0] = true;
    assert_eq!(live_vector(&problem, &live), vec![expected]);
    let (reduced, _) = DeadParamEliminator::new().eliminate(&problem);
    assert_eq!(reduced.predicates()[0].arity(), 1);
}

/// `P(x_0..x_n) -> P((ite G x_0 w) .. (ite G x_n w))` with one shared guard
/// `G` of `m` atoms: walking `G` once per argument costs `n * m` (~268 M node
/// visits here), the per-clause walked-node skip costs `n + m`.
#[test]
#[ntest::timeout(10_000)]
fn shared_subterm_is_walked_once_per_clause() {
    let n = 1 << 14;
    let m = 1 << 14;
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int; n]);
    let w = ChcExpr::Var(int_var("w"));
    let guard = Arc::new(op(
        ChcOp::And,
        (0..m)
            .map(|k| op(ChcOp::Lt, vec![w.clone(), ChcExpr::Int(k as i128)]))
            .collect(),
    ));
    let xs: Vec<ChcExpr> = (0..n)
        .map(|i| ChcExpr::Var(int_var(&format!("x{i}"))))
        .collect();
    let head_args = xs
        .iter()
        .map(|x| {
            ChcExpr::Op(
                ChcOp::Ite,
                vec![guard.clone(), Arc::new(x.clone()), Arc::new(w.clone())],
            )
        })
        .collect();
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, xs)], None),
        ClauseHead::Predicate(p, head_args),
    ));
    assert!(
        shares_inner_node_across_arguments(&problem.clauses()[0]),
        "the guard is still shared after add_clause"
    );
    let live = DeadParamEliminator::new().compute_live_positions(&problem);
    assert_eq!(live_vector(&problem, &live), vec![vec![true; n]]);
}

#[test]
fn stop_request_eliminates_nothing() {
    let problem = wide_problem(16);
    let _scope = ay_core::resource::enter_check_stop(Arc::new(|| true));
    let live = DeadParamEliminator::new().compute_live_positions(&problem);
    assert_eq!(live_vector(&problem, &live), vec![vec![true; 16]]);
    let result = Box::new(DeadParamEliminator::new()).transform(problem.clone());
    assert_eq!(result.problem.predicates()[0].arity(), 16);
}
