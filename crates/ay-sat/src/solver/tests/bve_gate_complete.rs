// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-bve-gate-complete`: gate-restricted elimination of variables that
//! also occur in non-gate clauses. Random circuits (AND, XOR and ITE gates
//! over earlier variables) with extra random clauses are solved with the
//! switch on; every model must satisfy the original clauses and every UNSAT
//! answer must match brute force, while the restriction must actually be used.

use super::*;

fn switched(value: Option<bool>) -> ay_core::sat_ab_test_override::Guard {
    ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        bve_gate_complete: value,
        ..Default::default()
    })
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u32) -> u32 {
        (self.next() % u64::from(n)) as u32
    }
    fn lit(&mut self, vars: u32) -> Literal {
        let var = Variable(self.below(vars));
        if self.next() & 1 == 0 {
            Literal::positive(var)
        } else {
            Literal::negative(var)
        }
    }
}

/// Inputs `0..inputs`, then one gate per variable up to `vars`, then `extra`
/// random clauses of length 2 or 3 over all variables. Variable `vars` is `z`,
/// false at the root (the caller assigns it): half the AND gates carry `z` in
/// a gate clause, which the extractor reads as binary through `vals`.
fn circuit(rng: &mut Rng, inputs: u32, vars: u32, extra: usize) -> Vec<Vec<Literal>> {
    let z = Literal::positive(Variable(vars));
    let mut clauses = vec![vec![z.negated()]];
    for out in inputs..vars {
        let x = Literal::positive(Variable(out));
        let a = rng.lit(out);
        let b = rng.lit(out);
        if a.variable() == b.variable() {
            // x = a
            clauses.push(vec![x.negated(), a]);
            clauses.push(vec![x, a.negated()]);
            continue;
        }
        match rng.below(3) {
            0 => {
                // x = a & b
                if rng.next() & 1 == 0 {
                    clauses.push(vec![x.negated(), a, z]);
                } else {
                    clauses.push(vec![x.negated(), a]);
                }
                clauses.push(vec![x.negated(), b]);
                clauses.push(vec![x, a.negated(), b.negated()]);
            }
            1 => {
                // x = a ^ b
                clauses.push(vec![x.negated(), a, b]);
                clauses.push(vec![x.negated(), a.negated(), b.negated()]);
                clauses.push(vec![x, a.negated(), b]);
                clauses.push(vec![x, a, b.negated()]);
            }
            _ => {
                let c = rng.lit(out);
                if c.variable() == a.variable() || c.variable() == b.variable() {
                    clauses.push(vec![x.negated(), a]);
                    clauses.push(vec![x, a.negated()]);
                    continue;
                }
                // x = a ? b : c
                clauses.push(vec![x.negated(), a.negated(), b]);
                clauses.push(vec![x, a.negated(), b.negated()]);
                clauses.push(vec![x.negated(), a, c]);
                clauses.push(vec![x, a, c.negated()]);
            }
        }
    }
    for _ in 0..extra {
        let len = 2 + rng.below(2) as usize;
        let mut clause: Vec<Literal> = Vec::with_capacity(len);
        while clause.len() < len {
            let lit = rng.lit(vars);
            if clause.iter().all(|l| l.variable() != lit.variable()) {
                clause.push(lit);
            }
        }
        clauses.push(clause);
    }
    clauses
}

fn satisfied(model: &[bool], clauses: &[Vec<Literal>]) -> bool {
    clauses.iter().all(|clause| {
        clause
            .iter()
            .any(|lit| model.get(lit.variable().index()).copied() == Some(lit.is_positive()))
    })
}

fn brute_force_sat(vars: u32, clauses: &[Vec<Literal>]) -> bool {
    (0..1u32 << vars).any(|mask| {
        let model: Vec<bool> = (0..vars).map(|v| mask >> v & 1 == 1).collect();
        satisfied(&model, clauses)
    })
}

/// The live irredundant clauses after BVE, plus a unit per root assignment.
fn remaining_formula(solver: &Solver, vars: u32) -> Vec<Vec<Literal>> {
    let mut remaining: Vec<Vec<Literal>> = solver
        .arena
        .indices()
        .filter(|&idx| !solver.arena.is_dead(idx) && !solver.arena.is_learned(idx))
        .map(|idx| solver.arena.literals(idx).to_vec())
        .collect();
    for v in 0..vars as usize {
        if let Some(value) = solver.get_var_assignment(v) {
            let var = Variable(v as u32);
            remaining.push(vec![if value {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            }]);
        }
    }
    remaining
}

/// Inprocessing BVE (the preprocessing pass does not use gates) at the
/// highest growth bound, so that the gate restriction is what decides. Checks
/// that the remaining formula is equisatisfiable with `clauses` and that
/// reconstruction turns EVERY model of it into a model of `clauses`; returns
/// the gates proved beside non-gate clauses.
fn eliminate_and_check(vars: u32, clauses: &[Vec<Literal>], round: u32) -> u64 {
    let expected = brute_force_sat(vars, clauses);
    let mut solver = Solver::new(vars as usize);
    for clause in clauses.iter().filter(|clause| clause.len() > 1) {
        solver.add_clause_db(clause, false);
    }
    solver.initialize_watches();
    for clause in clauses.iter().filter(|clause| clause.len() == 1) {
        let lit = clause[0];
        let v = lit.variable().index();
        solver.vals[lit.index()] = 1;
        solver.vals[lit.negated().index()] = -1;
        solver.var_data[v].level = 0;
        solver.var_data[v].trail_pos = solver.trail.len() as u32;
        solver.trail.push(lit);
    }
    solver.set_bve_enabled(true);
    solver.inproc.bve.reset_growth_bound_for_inprocessing();
    for _ in 0..5 {
        solver.inproc.bve.increment_growth_bound();
    }
    solver.inproc.bve.mark_all_candidates_dirty();
    if solver.bve() {
        assert!(
            !expected,
            "round {round}: BVE refuted a satisfiable formula"
        );
        return solver.bve_gate_profile().0;
    }
    let remaining = remaining_formula(&solver, vars);
    let mut any = false;
    for mask in 0..1u32 << vars {
        let model: Vec<bool> = (0..vars).map(|v| mask >> v & 1 == 1).collect();
        if !satisfied(&model, &remaining) {
            continue;
        }
        any = true;
        let mut extended = model.clone();
        solver.inproc.reconstruction.reconstruct(&mut extended);
        assert!(
            satisfied(&extended, clauses),
            "round {round}: reconstruction of {model:?} gives {extended:?}, not a model"
        );
    }
    assert_eq!(any, expected, "round {round}: BVE changed satisfiability");
    solver.bve_gate_profile().0
}

#[test]
fn restricted_elimination_beside_non_gate_clauses_is_sound() {
    let _guard = switched(Some(true));
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let (mut sat, mut proved) = (0, 0);
    for round in 0..400 {
        let inputs = 3 + rng.below(3);
        let vars = inputs + 5 + rng.below(5);
        let extra = rng.below(2 + vars) as usize;
        let clauses = circuit(&mut rng, inputs, vars, extra);
        sat += u32::from(brute_force_sat(vars + 1, &clauses));
        proved += eliminate_and_check(vars + 1, &clauses, round);
    }
    assert!(sat > 0 && sat < 400, "sat={sat} of 400");
    assert!(
        proved > 0,
        "no gate restriction beside non-gate clauses was used"
    );
}
