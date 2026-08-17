// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `group_soundness::soundness_expanded_7904` to preserve item paths.

// ---------------------------------------------------------------------------
// Formula generators: Tseitin encoding
// ---------------------------------------------------------------------------

/// Generate a Tseitin formula on a cycle graph with `n` vertices.
/// XOR parity constraint on a cycle: UNSAT for odd n, SAT for even n.
fn generate_tseitin_cycle(n: usize) -> (usize, Vec<Vec<Literal>>) {
    let num_vars = n;
    let mut clauses = Vec::new();

    for v in 0..n {
        let e_prev = Variable::new(((v + n - 1) % n) as u32);
        let e_curr = Variable::new(v as u32);

        // e_prev XOR e_curr = 1
        clauses.push(vec![Literal::positive(e_prev), Literal::positive(e_curr)]);
        clauses.push(vec![Literal::negative(e_prev), Literal::negative(e_curr)]);
    }

    (num_vars, clauses)
}

/// Generate a Tseitin formula on a complete graph K_n.
/// With odd parity assignment on each vertex, UNSAT for odd n.
fn generate_tseitin_complete(n: usize) -> (usize, Vec<Vec<Literal>>) {
    let num_edges = n * (n - 1) / 2;
    let mut clauses = Vec::new();

    let edge_var = |i: usize, j: usize| -> u32 {
        let (a, b) = if i < j { (i, j) } else { (j, i) };
        let base: usize = (0..a).map(|k| n - 1 - k).sum();
        (base + b - a - 1) as u32
    };

    for v in 0..n {
        let mut incident: Vec<u32> = Vec::new();
        for u in 0..n {
            if u != v {
                incident.push(edge_var(v, u));
            }
        }

        if incident.is_empty() {
            continue;
        }
        if incident.len() == 1 {
            clauses.push(vec![Literal::positive(Variable::new(incident[0]))]);
            continue;
        }

        let aux_base = num_edges as u32 + (v * (n - 1)) as u32;
        let a0 = Variable::new(aux_base);
        let e0 = Variable::new(incident[0]);
        clauses.push(vec![Literal::positive(a0), Literal::negative(e0)]);
        clauses.push(vec![Literal::negative(a0), Literal::positive(e0)]);

        for (i, &edge_var) in incident.iter().enumerate().skip(1) {
            let a_prev = Variable::new(aux_base + (i - 1) as u32);
            let ei = Variable::new(edge_var);
            let a_curr = Variable::new(aux_base + i as u32);

            clauses.push(vec![
                Literal::negative(a_curr),
                Literal::negative(a_prev),
                Literal::negative(ei),
            ]);
            clauses.push(vec![
                Literal::negative(a_curr),
                Literal::positive(a_prev),
                Literal::positive(ei),
            ]);
            clauses.push(vec![
                Literal::positive(a_curr),
                Literal::negative(a_prev),
                Literal::positive(ei),
            ]);
            clauses.push(vec![
                Literal::positive(a_curr),
                Literal::positive(a_prev),
                Literal::negative(ei),
            ]);
        }

        let a_last = Variable::new(aux_base + (incident.len() - 1) as u32);
        clauses.push(vec![Literal::positive(a_last)]);
    }

    let total_vars = num_edges + n * (n - 1);
    (total_vars, clauses)
}

// ---------------------------------------------------------------------------
// Formula generators: XOR / parity constraints
// ---------------------------------------------------------------------------

/// XOR cycle of length n: x_i XOR x_{(i+1)%n} = 1 for all i.
/// UNSAT for odd n (circular XOR contradiction).
fn generate_xor_unsat(n: usize) -> (usize, Vec<Vec<Literal>>) {
    let mut clauses = Vec::new();
    for i in 0..n {
        let vi = Variable::new(i as u32);
        let vj = Variable::new(((i + 1) % n) as u32);
        clauses.push(vec![Literal::positive(vi), Literal::positive(vj)]);
        clauses.push(vec![Literal::negative(vi), Literal::negative(vj)]);
    }
    (n, clauses)
}

/// Parity constraint: all n variables forced true + XOR = 1.
/// UNSAT for even n (XOR of even number of true values = 0, not 1).
fn generate_parity_unsat(n: usize) -> (usize, Vec<Vec<Literal>>) {
    assert!(n >= 2 && n.is_multiple_of(2));
    let aux_base = n as u32;
    let total_vars = n + (n - 1);
    let mut clauses = Vec::new();

    for i in 0..n {
        clauses.push(vec![Literal::positive(Variable::new(i as u32))]);
    }

    let a0 = Variable::new(aux_base);
    let x0 = Variable::new(0);
    clauses.push(vec![Literal::positive(a0), Literal::negative(x0)]);
    clauses.push(vec![Literal::negative(a0), Literal::positive(x0)]);

    for i in 1..n {
        let a_prev = Variable::new(aux_base + (i - 1) as u32);
        let xi = Variable::new(i as u32);
        let a_curr = Variable::new(aux_base + i as u32);

        if i < n - 1 {
            clauses.push(vec![
                Literal::negative(a_curr),
                Literal::negative(a_prev),
                Literal::negative(xi),
            ]);
            clauses.push(vec![
                Literal::negative(a_curr),
                Literal::positive(a_prev),
                Literal::positive(xi),
            ]);
            clauses.push(vec![
                Literal::positive(a_curr),
                Literal::negative(a_prev),
                Literal::positive(xi),
            ]);
            clauses.push(vec![
                Literal::positive(a_curr),
                Literal::positive(a_prev),
                Literal::negative(xi),
            ]);
        } else {
            // Last step: assert a_prev XOR xi = 1
            clauses.push(vec![Literal::positive(a_prev), Literal::positive(xi)]);
            clauses.push(vec![Literal::negative(a_prev), Literal::negative(xi)]);
        }
    }

    (total_vars, clauses)
}

// ---------------------------------------------------------------------------
// Formula generators: Cardinality constraints
// ---------------------------------------------------------------------------

/// At-most-k of n variables, with k+1 forced true => UNSAT.
fn generate_cardinality_unsat(n: usize, k: usize) -> (usize, Vec<Vec<Literal>>) {
    assert!(k < n);
    let mut clauses = Vec::new();
    let vars: Vec<Variable> = (0..n).map(|i| Variable::new(i as u32)).collect();

    fn enumerate_subsets(
        n: usize,
        size: usize,
        start: usize,
        depth: usize,
        subset: &mut Vec<usize>,
        vars: &[Variable],
        clauses: &mut Vec<Vec<Literal>>,
    ) {
        if depth == size {
            let clause: Vec<Literal> = subset[..size]
                .iter()
                .map(|&i| Literal::negative(vars[i]))
                .collect();
            clauses.push(clause);
            return;
        }
        for i in start..n {
            subset[depth] = i;
            enumerate_subsets(n, size, i + 1, depth + 1, subset, vars, clauses);
        }
    }

    let mut subset = vec![0usize; k + 1];
    enumerate_subsets(n, k + 1, 0, 0, &mut subset, &vars, &mut clauses);

    for v in &vars[..=k] {
        clauses.push(vec![Literal::positive(*v)]);
    }

    (n, clauses)
}

// ---------------------------------------------------------------------------
// Formula generators: Latin square
// ---------------------------------------------------------------------------

/// 2x2 Latin square with conflicting assignment (UNSAT).
fn generate_latin_square_unsat() -> (usize, Vec<Vec<Literal>>) {
    let num_vars = 8;
    let var =
        |r: usize, c: usize, v: usize| -> Variable { Variable::new((r * 4 + c * 2 + v) as u32) };

    let mut clauses = Vec::new();

    for r in 0..2 {
        for c in 0..2 {
            clauses.push(vec![
                Literal::positive(var(r, c, 0)),
                Literal::positive(var(r, c, 1)),
            ]);
        }
    }
    for r in 0..2 {
        for c in 0..2 {
            clauses.push(vec![
                Literal::negative(var(r, c, 0)),
                Literal::negative(var(r, c, 1)),
            ]);
        }
    }
    for r in 0..2 {
        for v in 0..2 {
            clauses.push(vec![
                Literal::negative(var(r, 0, v)),
                Literal::negative(var(r, 1, v)),
            ]);
        }
    }
    for c in 0..2 {
        for v in 0..2 {
            clauses.push(vec![
                Literal::negative(var(0, c, v)),
                Literal::negative(var(1, c, v)),
            ]);
        }
    }
    // Conflicting: cell (0,0)=val0 and cell (0,1)=val0
    clauses.push(vec![Literal::positive(var(0, 0, 0))]);
    clauses.push(vec![Literal::positive(var(0, 1, 0))]);

    (num_vars, clauses)
}
