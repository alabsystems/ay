// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A leaf's core SWEPT (`crate::sat_sweep`) instead of searched.
//!
//! ## Why
//!
//! Once a leaf's wiring is collapsed (`leaf.rs`), what is left is often an
//! identity between two circuits whose internal signals line up: on
//! proof_gate_strict row 1257 the negative case is `-(-a) = a`, and carry
//! `i` of the outer negation equals carry `i` of the inner one. The solver
//! found it as ~700 learned clauses of ~24 hints per leaf (18.7 MB of the
//! printed document over 54 leaves); a sweep proves each carry equal in a
//! few hints.
//!
//! ## What it does
//!
//! Each core variable that is a gate keeps its gate over the core's own
//! variables (operands through their representatives, the leaf's values
//! folded in); every other one is free. A core clause that is no core
//! gate's row is a root. The sweep's refutation is over the core's clauses,
//! so it is used exactly as the solver's would be.

use super::super::*;
use super::pool::Pool;

/// The leaf's core, as the sweep needs it.
pub(super) struct Core<'c> {
    pub(super) nodes: &'c [Gate],
    pub(super) value: &'c [Option<bool>],
    pub(super) rep: &'c DetHashMap<Literal, Literal>,
    pub(super) pool: &'c Pool,
    /// The pool clause each core clause was rewritten from.
    pub(super) sources: &'c [usize],
    pub(super) clauses: &'c [Vec<Literal>],
    /// The global variable of each core variable, in ascending order.
    pub(super) global: &'c [usize],
    pub(super) local_of: &'c DetHashMap<usize, usize>,
}

enum Operand {
    Const(bool),
    Lit(Literal),
}

impl Core<'_> {
    fn operand(&self, lit: Literal) -> Option<Operand> {
        if let Some(value) = self.value[lit.variable().index()] {
            return Some(Operand::Const(value == lit.is_positive()));
        }
        let rep = self.rep.get(&lit).copied().unwrap_or(lit);
        let local = *self.local_of.get(&rep.variable().index())?;
        Some(Operand::Lit(literal(local, !rep.is_positive())))
    }

    /// The core gate of global variable `var`, or `Input`.
    fn gate(&self, var: usize) -> Gate {
        self.fold(var).unwrap_or(Gate::Input)
    }

    fn fold(&self, var: usize) -> Option<Gate> {
        Some(match &self.nodes[var] {
            Gate::And(args) | Gate::Or(args) => {
                // The value one operand forces: false for `and`, true for `or`.
                let forcing = matches!(self.nodes[var], Gate::Or(_));
                let mut kept: Vec<Literal> = Vec::new();
                for arg in args {
                    match self.operand(*arg)? {
                        Operand::Const(value) if value == forcing => {
                            return Some(Gate::Const(forcing))
                        }
                        Operand::Const(_) => {}
                        Operand::Lit(lit) => kept.push(lit),
                    }
                }
                match kept.len() {
                    0 => Gate::Const(!forcing),
                    1 => Gate::Alias(kept[0]),
                    _ if forcing => Gate::Or(kept),
                    _ => Gate::And(kept),
                }
            }
            Gate::Xor(args) => {
                let mut flip = false;
                let mut kept: Vec<Literal> = Vec::new();
                for arg in args {
                    match self.operand(*arg)? {
                        Operand::Const(value) => flip ^= value,
                        Operand::Lit(lit) => kept.push(lit),
                    }
                }
                if flip {
                    let first = kept.first_mut()?;
                    *first = first.negated();
                }
                match kept.len() {
                    0 => Gate::Const(flip),
                    1 => Gate::Alias(kept[0]),
                    _ => Gate::Xor(kept),
                }
            }
            Gate::Iff(a, b) => match (self.operand(*a)?, self.operand(*b)?) {
                (Operand::Lit(a), Operand::Lit(b)) => Gate::Iff(a, b),
                (Operand::Const(value), Operand::Lit(lit))
                | (Operand::Lit(lit), Operand::Const(value)) => {
                    Gate::Alias(if value { lit } else { lit.negated() })
                }
                (Operand::Const(a), Operand::Const(b)) => Gate::Const(a == b),
            },
            Gate::Ite(c, a, b) => match self.operand(*c)? {
                Operand::Const(true) => self.alias(*a)?,
                Operand::Const(false) => self.alias(*b)?,
                Operand::Lit(c) => match (self.operand(*a)?, self.operand(*b)?) {
                    (Operand::Lit(a), Operand::Lit(b)) => Gate::Ite(c, a, b),
                    _ => return None,
                },
            },
            Gate::Majority(a, b, c) => {
                let (a, b, c) = (self.operand(*a)?, self.operand(*b)?, self.operand(*c)?);
                match (a, b, c) {
                    (Operand::Lit(a), Operand::Lit(b), Operand::Lit(c)) => Gate::Majority(a, b, c),
                    (Operand::Const(value), Operand::Lit(x), Operand::Lit(y))
                    | (Operand::Lit(x), Operand::Const(value), Operand::Lit(y))
                    | (Operand::Lit(x), Operand::Lit(y), Operand::Const(value)) => {
                        if value {
                            Gate::Or(vec![x, y])
                        } else {
                            Gate::And(vec![x, y])
                        }
                    }
                    _ => return None,
                }
            }
            Gate::Alias(target) => self.alias(*target)?,
            Gate::Input | Gate::Const(_) | Gate::GuardedIte { .. } => return None,
        })
    }

    fn alias(&self, lit: Literal) -> Option<Gate> {
        Some(match self.operand(lit)? {
            Operand::Const(value) => Gate::Const(value),
            Operand::Lit(lit) => Gate::Alias(lit),
        })
    }

    /// The core's refutation by a sweep within `limits`, or `None`, and what
    /// the sweep spent. The sweep polls `keep_going`, the enclosing
    /// split's own poll (`Sweep::refute_core`): `limits` carries only the
    /// split's counted envelope and hang guard, so a leaf swept under an
    /// unconditional poll outlived its caller's stop. Measured on the
    /// strict checker's lemma `(bvult (bvmul P12 P7) (bvmul Q7 Q12))`, the
    /// sign-extended 32-bit products with commuted operands, under a 20 s
    /// query timeout: no poll for 43.6 s, the query `unknown` at 48.4 s.
    pub(super) fn sweep(
        &self,
        limits: SweepLimits,
        keep_going: &mut dyn FnMut() -> bool,
    ) -> (Option<ResolutionDag>, work::Spent) {
        if !keep_going() {
            return (None, work::Spent::default());
        }
        let mut gates: Vec<Gate> = self.global.iter().map(|&var| self.gate(var)).collect();
        let order = topological(&mut gates);
        // A core clause rewritten from a row of a core gate belongs to that
        // gate; every other one is a root.
        let roots: Vec<usize> = self
            .sources
            .iter()
            .enumerate()
            .filter(|(_, &source)| {
                !self.pool.clauses[source].iter().any(|lit| {
                    let var = lit.variable().index();
                    self.local_of
                        .get(&var)
                        .is_some_and(|&local| !matches!(gates[local], Gate::Input))
                        && self.pool.rows[var].contains(&(source as u32))
                })
            })
            .map(|(index, _)| index)
            .collect();
        // The sweep simulates and merges in variable order, so it sees the
        // core renumbered operands first; its refutation is renumbered back.
        let mut position = vec![0usize; order.len()];
        for (at, &local) in order.iter().enumerate() {
            position[local] = at;
        }
        let rename = |lit: &Literal| literal(position[lit.variable().index()], !lit.is_positive());
        let renamed: Vec<Gate> = order
            .iter()
            .map(|&local| renamed_gate(&gates[local], &rename))
            .collect();
        let clauses: Vec<Vec<Literal>> = self
            .clauses
            .iter()
            .map(|clause| clause.iter().map(rename).collect())
            .collect();
        let (dag, spent) = refute_counted(renamed, &clauses, &roots, false, limits, keep_going);
        let dag = dag.map(|mut dag| {
            for step in &mut dag.derived {
                for lit in &mut step.clause {
                    *lit = literal(order[lit.variable().index()], !lit.is_positive());
                }
            }
            dag
        });
        (dag, spent)
    }
}

fn renamed_gate(gate: &Gate, rename: &dyn Fn(&Literal) -> Literal) -> Gate {
    match gate {
        Gate::Input => Gate::Input,
        Gate::Const(value) => Gate::Const(*value),
        Gate::And(args) => Gate::And(args.iter().map(rename).collect()),
        Gate::Or(args) => Gate::Or(args.iter().map(rename).collect()),
        Gate::Xor(args) => Gate::Xor(args.iter().map(rename).collect()),
        Gate::Iff(a, b) => Gate::Iff(rename(a), rename(b)),
        Gate::Ite(c, a, b) => Gate::Ite(rename(c), rename(a), rename(b)),
        Gate::Majority(a, b, c) => Gate::Majority(rename(a), rename(b), rename(c)),
        Gate::Alias(target) => Gate::Alias(rename(target)),
        // `fold` makes none: a guarded bit is free in a core.
        Gate::GuardedIte { .. } => Gate::Input,
    }
}

/// The core variables with every gate after its operands; a gate on a
/// cycle (possible once equal literals share a representative) becomes free.
fn topological(gates: &mut [Gate]) -> Vec<usize> {
    const NEW: u8 = 0;
    const OPEN: u8 = 1;
    const DONE: u8 = 2;
    let mut state = vec![NEW; gates.len()];
    let mut order: Vec<usize> = Vec::with_capacity(gates.len());
    for start in 0..gates.len() {
        if state[start] != NEW {
            continue;
        }
        let mut frames: Vec<(usize, usize)> = vec![(start, 0)];
        state[start] = OPEN;
        while let Some(&mut (node, ref mut next)) = frames.last_mut() {
            let operands = gates[node].operands();
            if let Some(&operand) = operands.get(*next) {
                *next += 1;
                match state[operand] {
                    NEW => {
                        state[operand] = OPEN;
                        frames.push((operand, 0));
                    }
                    OPEN => {
                        // A cycle: this gate is not a function of the rest.
                        gates[node] = Gate::Input;
                        if let Some(frame) = frames.last_mut() {
                            frame.1 = usize::MAX;
                        }
                    }
                    _ => {}
                }
                continue;
            }
            frames.pop();
            state[node] = DONE;
            order.push(node);
        }
    }
    order
}
