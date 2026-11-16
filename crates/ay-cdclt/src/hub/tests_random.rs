// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The hub against a brute-force congruence closure, with backtracking and
//! explanations, on random instances.

use ay_core::TermId;

use super::{Hub, NodeId};

fn t(i: u32) -> TermId {
    TermId(i)
}

/// A tiny xorshift for the randomized tests.
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }
}

/// Congruence closure of `eqs` over `apps` by brute force: a union-find
/// iterated to a fixpoint. Returns each node's representative.
fn naive_closure(
    n: usize,
    apps: &[(NodeId, u32, Vec<NodeId>)],
    eqs: &[(NodeId, NodeId)],
) -> Vec<usize> {
    let mut parent: Vec<usize> = (0..n).collect();
    fn find(p: &mut [usize], x: usize) -> usize {
        let mut r = x;
        while p[r] != r {
            r = p[r];
        }
        p[x] = r;
        r
    }
    for &(x, y) in eqs {
        let (rx, ry) = (find(&mut parent, x as usize), find(&mut parent, y as usize));
        parent[rx] = ry;
    }
    loop {
        let mut changed = false;
        for i in 0..apps.len() {
            for j in i + 1..apps.len() {
                let (ni, fi, ai) = &apps[i];
                let (nj, fj, aj) = &apps[j];
                if fi != fj || ai.len() != aj.len() {
                    continue;
                }
                let same = ai
                    .iter()
                    .zip(aj)
                    .all(|(&x, &y)| find(&mut parent, x as usize) == find(&mut parent, y as usize));
                let (ri, rj) = (
                    find(&mut parent, *ni as usize),
                    find(&mut parent, *nj as usize),
                );
                if same && ri != rj {
                    parent[ri] = rj;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    (0..n).map(|x| find(&mut parent, x)).collect()
}

/// A hub over five leaves, twelve random `f`/`g` applications and ten
/// equality atoms between random terms.
struct RandomHub {
    hub: Hub,
    terms: Vec<NodeId>,
    apps: Vec<(NodeId, u32, Vec<NodeId>)>,
    atoms: Vec<(NodeId, NodeId, NodeId)>,
}

fn random_hub(rng: &mut Rng) -> RandomHub {
    let u = ay_core::Sort::Uninterpreted("U".to_string());
    let mut hub = Hub::sparse(t(0), t(1));
    let mut next = 10u32;
    let mut fresh = || {
        next += 1;
        t(next)
    };
    let mut terms: Vec<NodeId> = (0..5).map(|_| hub.add_leaf(fresh(), false, None)).collect();
    let f = hub.func_id("f", 1, &u);
    let g = hub.func_id("g", 2, &u);
    let mut apps: Vec<(NodeId, u32, Vec<NodeId>)> = Vec::new();
    for _ in 0..12 {
        let (func, args) = if rng.below(2) == 0 {
            (f, vec![terms[rng.below(terms.len())]])
        } else {
            let (x, y) = (terms[rng.below(terms.len())], terms[rng.below(terms.len())]);
            (g, vec![x, y])
        };
        let n = hub.add_app(fresh(), func, args.clone(), false);
        apps.push((n, func, args));
        terms.push(n);
    }
    let mut atoms: Vec<(NodeId, NodeId, NodeId)> = Vec::new();
    for _ in 0..10 {
        let (x, y) = (terms[rng.below(terms.len())], terms[rng.below(terms.len())]);
        if x != y {
            let e = hub.add_eq(fresh(), x, y);
            atoms.push((e, x, y));
        }
    }
    RandomHub {
        hub,
        terms,
        apps,
        atoms,
    }
}

/// Random equalities asserted and retracted in scopes: after every closure
/// the hub's classes are the brute-force congruence closure of the asserted
/// equalities, and every explanation is sound (its literals are asserted)
/// and sufficient (their closure alone joins the pair).
#[test]
fn random_congruence_matches_the_naive_closure_with_explanations() {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let mut explained = 0;
    for round in 0..60 {
        let RandomHub {
            mut hub,
            terms,
            apps,
            atoms,
        } = random_hub(&mut rng);
        hub.propagate();
        let total = hub.len();
        // The asserted equalities per open scope.
        let mut scopes: Vec<Vec<usize>> = vec![Vec::new()];
        for step in 0..40 {
            match rng.below(5) {
                0 if scopes.len() > 1 => {
                    let k = 1 + rng.below(scopes.len() - 1);
                    scopes.truncate(scopes.len() - k);
                    hub.pop_scopes(k);
                }
                1 => {
                    scopes.push(Vec::new());
                    hub.push_scope();
                }
                _ if !atoms.is_empty() => {
                    let i = rng.below(atoms.len());
                    if scopes.len() == 1 {
                        scopes.push(Vec::new());
                        hub.push_scope();
                    }
                    hub.assign(atoms[i].0, true);
                    if let Some(top) = scopes.last_mut() {
                        top.push(i);
                    }
                }
                _ => {}
            }
            hub.propagate();
            assert!(hub.take_conflict().is_none(), "round {round} step {step}");
            let _ = (hub.take_events(), hub.take_props());
            let asserted: Vec<usize> = scopes.iter().flatten().copied().collect();
            let eqs: Vec<(NodeId, NodeId)> =
                asserted.iter().map(|&i| (atoms[i].1, atoms[i].2)).collect();
            let expect = naive_closure(total, &apps, &eqs);
            for &x in &terms {
                for &y in &terms {
                    let same = hub.root(x) == hub.root(y);
                    assert_eq!(
                        same,
                        expect[x as usize] == expect[y as usize],
                        "round {round} step {step}: {x} ~ {y}"
                    );
                    if !same || x >= y {
                        continue;
                    }
                    let why = hub.explain(x, y).expect("same class has a path");
                    explained += 1;
                    let mut used = Vec::new();
                    for lit in &why {
                        assert!(lit.value, "only true equalities were asserted");
                        let i = atoms
                            .iter()
                            .position(|&(e, _, _)| hub.term(e) == lit.term)
                            .expect("an explanation names an atom");
                        assert!(
                            asserted.contains(&i),
                            "round {round}: {lit:?} is not asserted"
                        );
                        used.push((atoms[i].1, atoms[i].2));
                    }
                    let alone = naive_closure(total, &apps, &used);
                    assert_eq!(
                        alone[x as usize], alone[y as usize],
                        "round {round} step {step}: the explanation of {x} ~ {y} is not enough"
                    );
                }
            }
        }
    }
    assert!(explained > 1000, "explanations were exercised: {explained}");
}
