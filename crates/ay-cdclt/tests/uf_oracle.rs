// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Random Boolean combinations of equalities and predicates over one
//! uninterpreted sort, decided by the engine (the hub and the EUF plug-in)
//! and by an independent oracle.
//!
//! Terms: constants `c0..c3`, a unary `f`, a binary `g`, and `h` from Bool
//! to the sort applied to the Bool variables `q0`, `q1`, to `true` and to
//! `¬q0`.
//! Atoms: equalities between random terms, the predicate `p` on random
//! terms, and `q0`, `q1` themselves.
//!
//! Oracle: a model induces a partition of the ground terms that is closed
//! under congruence, and every such partition is induced by a model (the
//! sort is infinite, distinct classes get distinct elements). So the input
//! is satisfiable iff for some assignment of `q0`, `q1`, some partition of
//! the terms closed under congruence (with `h`'s argument identified by its
//! truth value), and some value of `p` per class, every clause holds. The
//! oracle enumerates exactly that; every `sat` answer is also checked by the
//! engine's independent evaluator, which verifies that the model is a
//! function.

use ay_cdclt::{Engine, EngineConfig, Guard, ModelVerdict, Verdict};
use ay_core::{Sort, Symbol, TermId, TermStore};

#[derive(Clone, Debug, PartialEq, Eq)]
enum T {
    C(usize),
    F(Box<T>),
    G(Box<T>, Box<T>),
    /// `h(q0)`, `h(q1)`, `h(true)`, `h(¬q0)`.
    H(usize),
}

#[derive(Clone, Debug)]
enum Atom {
    Eq(T, T),
    P(T),
    Q(usize),
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next() % n).unwrap_or(0)
    }
}

fn random_term(rng: &mut Rng, depth: u32) -> T {
    match (depth, rng.below(10)) {
        (0, _) | (_, 0..=3) => T::C(rng.below(4)),
        (_, 4..=6) => T::F(Box::new(random_term(rng, depth - 1))),
        (_, 7..=8) => T::G(
            Box::new(random_term(rng, depth - 1)),
            Box::new(random_term(rng, depth - 1)),
        ),
        _ => T::H(rng.below(4)),
    }
}

struct Instance {
    atoms: Vec<Atom>,
    clauses: Vec<Vec<(usize, bool)>>,
}

/// Instances over at most 8 distinct terms (Bell(8) = 4140 partitions).
fn random_instance(rng: &mut Rng) -> Instance {
    loop {
        let inst = random_instance_any(rng);
        let mut terms = Vec::new();
        for atom in &inst.atoms {
            match atom {
                Atom::Eq(a, b) => {
                    subterms(a, &mut terms);
                    subterms(b, &mut terms);
                }
                Atom::P(a) => subterms(a, &mut terms),
                Atom::Q(_) => {}
            }
        }
        if terms.len() <= 8 {
            return inst;
        }
    }
}

fn random_instance_any(rng: &mut Rng) -> Instance {
    let n_atoms = 4 + rng.below(3);
    let atoms = (0..n_atoms)
        .map(|_| match rng.below(10) {
            0..=5 => Atom::Eq(random_term(rng, 2), random_term(rng, 2)),
            6..=8 => Atom::P(random_term(rng, 2)),
            _ => Atom::Q(rng.below(2)),
        })
        .collect();
    let clauses = (0..3 + rng.below(5))
        .map(|_| {
            (0..=rng.below(3))
                .map(|_| (rng.below(n_atoms as u64), rng.below(2) == 0))
                .collect()
        })
        .collect();
    Instance { atoms, clauses }
}

// ---------------------------------------------------------------- oracle ---

fn subterms(t: &T, out: &mut Vec<T>) {
    match t {
        T::F(a) => subterms(a, out),
        T::G(a, b) => {
            subterms(a, out);
            subterms(b, out);
        }
        _ => {}
    }
    if !out.contains(t) {
        out.push(t.clone());
    }
}

/// Every restricted-growth string of length `n`: the set partitions.
fn partitions(n: usize, f: &mut impl FnMut(&[usize]) -> bool) -> bool {
    fn go(
        cls: &mut Vec<usize>,
        n: usize,
        max: usize,
        f: &mut impl FnMut(&[usize]) -> bool,
    ) -> bool {
        if cls.len() == n {
            return f(cls);
        }
        for c in 0..=max {
            cls.push(c);
            let next = if c == max { max + 1 } else { max };
            if go(cls, n, next, f) {
                return true;
            }
            cls.pop();
        }
        false
    }
    go(&mut Vec::new(), n, 0, f)
}

fn oracle(inst: &Instance) -> bool {
    let mut terms = Vec::new();
    for atom in &inst.atoms {
        match atom {
            Atom::Eq(a, b) => {
                subterms(a, &mut terms);
                subterms(b, &mut terms);
            }
            Atom::P(a) => subterms(a, &mut terms),
            Atom::Q(_) => {}
        }
    }
    let idx = |t: &T| terms.iter().position(|u| u == t).expect("subterm");
    (0..4u32).any(|qs| {
        // H(2) is h(true), H(3) is h(¬q0)
        let q = |i: usize| match i {
            2 => true,
            3 => qs & 1 == 0,
            _ => qs >> i & 1 == 1,
        };
        partitions(terms.len(), &mut |cls: &[usize]| {
            // congruence closure: congruent applications share a class
            for (i, a) in terms.iter().enumerate() {
                for (j, b) in terms.iter().enumerate().skip(i + 1) {
                    let congruent = match (a, b) {
                        (T::F(x), T::F(y)) => cls[idx(x)] == cls[idx(y)],
                        (T::G(x1, x2), T::G(y1, y2)) => {
                            cls[idx(x1)] == cls[idx(y1)] && cls[idx(x2)] == cls[idx(y2)]
                        }
                        (T::H(x), T::H(y)) => q(*x) == q(*y),
                        _ => false,
                    };
                    if congruent && cls[i] != cls[j] {
                        return false;
                    }
                }
            }
            // p per class of its arguments
            let p_classes: Vec<usize> = inst
                .atoms
                .iter()
                .filter_map(|a| match a {
                    Atom::P(t) => Some(cls[idx(t)]),
                    _ => None,
                })
                .collect();
            let mut distinct = p_classes.clone();
            distinct.sort_unstable();
            distinct.dedup();
            (0..1u32 << distinct.len()).any(|ps| {
                let p_of = |c: usize| {
                    let k = distinct.iter().position(|&d| d == c).expect("class");
                    ps >> k & 1 == 1
                };
                let value = |atom: &Atom| match atom {
                    Atom::Eq(a, b) => cls[idx(a)] == cls[idx(b)],
                    Atom::P(t) => p_of(cls[idx(t)]),
                    Atom::Q(i) => q(*i),
                };
                inst.clauses
                    .iter()
                    .all(|c| c.iter().any(|&(a, pos)| value(&inst.atoms[a]) == pos))
            })
        })
    })
}

// ---------------------------------------------------------------- engine ---

struct Builder {
    terms: TermStore,
    sort: Sort,
    q: [TermId; 2],
}

impl Builder {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let q = [
            terms.mk_var("q0", Sort::Bool),
            terms.mk_var("q1", Sort::Bool),
        ];
        Self {
            terms,
            sort: Sort::Uninterpreted("U".to_string()),
            q,
        }
    }

    fn term(&mut self, t: &T) -> TermId {
        match t {
            T::C(i) => self.terms.mk_var(format!("c{i}"), self.sort.clone()),
            T::F(a) => {
                let a = self.term(a);
                self.terms
                    .mk_app(Symbol::named("f"), vec![a], self.sort.clone())
            }
            T::G(a, b) => {
                let (a, b) = (self.term(a), self.term(b));
                self.terms
                    .mk_app(Symbol::named("g"), vec![a, b], self.sort.clone())
            }
            T::H(i) => {
                let arg = match *i {
                    2 => self.terms.mk_bool(true),
                    3 => self.terms.mk_not(self.q[0]),
                    _ => self.q[*i],
                };
                self.terms
                    .mk_app(Symbol::named("h"), vec![arg], self.sort.clone())
            }
        }
    }

    fn atom(&mut self, a: &Atom) -> TermId {
        match a {
            Atom::Eq(x, y) => {
                let (x, y) = (self.term(x), self.term(y));
                self.terms.mk_eq(x, y)
            }
            Atom::P(x) => {
                let x = self.term(x);
                self.terms.mk_app(Symbol::named("p"), vec![x], Sort::Bool)
            }
            Atom::Q(i) => self.q[*i],
        }
    }
}

#[test]
fn engine_agrees_with_the_partition_oracle() {
    let mut rng = Rng(0x2545_F491_4F6C_DD1D);
    let (mut sat, mut unsat, mut merges, mut conflicts) = (0, 0, 0, 0);
    for round in 0..1500 {
        let inst = random_instance(&mut rng);
        let expected = oracle(&inst);
        let mut b = Builder::new();
        let atom_terms: Vec<TermId> = inst.atoms.iter().map(|a| b.atom(a)).collect();
        let roots: Vec<TermId> = inst
            .clauses
            .iter()
            .map(|c| {
                let lits = c
                    .iter()
                    .map(|&(a, pos)| {
                        if pos {
                            atom_terms[a]
                        } else {
                            b.terms.mk_not(atom_terms[a])
                        }
                    })
                    .collect();
                b.terms.mk_or(lits)
            })
            .collect();
        // Odd rounds run the relevancy filter (KC21): it must not change a
        // verdict.
        let mut engine = Engine::new(EngineConfig {
            hub_relevancy: round % 2 == 1,
            ..EngineConfig::default()
        });
        for &r in &roots {
            engine.assert(r);
        }
        let checked = engine.check(&mut b.terms, &[], &Guard::new());
        let stats = checked.stats.clone();
        let outcome = match checked.verdict {
            Verdict::Sat => Out::Sat,
            Verdict::Unsat => Out::Unsat,
            Verdict::Unknown => Out::Unknown(checked.reason.clone().unwrap_or_default()),
        };
        assert!(stats.solve_calls <= 1, "round {round}: {stats:?}");
        merges += stats.hub_merges;
        conflicts += stats.hub_conflicts;
        match outcome {
            Out::Sat => {
                assert!(expected, "round {round}: wrong sat on {:?}", inst.atoms);
                assert_eq!(
                    engine.check_model(&mut b.terms, &roots),
                    ModelVerdict::Satisfied,
                    "round {round}: model check on {:?} {:?}",
                    inst.atoms,
                    inst.clauses
                );
                sat += 1;
            }
            Out::Unsat => {
                assert!(
                    !expected,
                    "round {round}: wrong unsat on {:?} {:?}",
                    inst.atoms, inst.clauses
                );
                unsat += 1;
            }
            Out::Unknown(reason) => {
                panic!("round {round}: unknown ({reason}) on {:?}", inst.atoms)
            }
        }
    }
    eprintln!(
        "uf oracle: {sat} sat, {unsat} unsat, {merges} hub merges, {conflicts} hub conflicts"
    );
    assert!(
        sat > 200 && unsat > 200,
        "a useful mix: {sat} sat, {unsat} unsat"
    );
    assert!(merges > 0 && conflicts > 0, "the hub was exercised");
}

/// A check's verdict, with the unknown reason.
#[derive(Debug)]
enum Out {
    Sat,
    Unsat,
    Unknown(String),
}
