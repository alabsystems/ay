// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Combinatorial hard formula generators for proof complexity analysis.
//!
//! These formulas are known to require large proofs in certain proof systems:
//! - Pigeonhole principle (exponential for resolution)
//! - Parity (exponential for resolution)
//! - Ordering principle (exponential for tree-resolution)
//! - Random k-CNF (hard near the satisfiability threshold)

use rand::prelude::*;
use rand_chacha::ChaCha8Rng;

use crate::cnf::{add_xor_equals_clauses, xor_clause_count, Cnf};
use crate::{Lit, Var};

/// Generate the Pigeonhole Principle formula: n+1 pigeons into n holes.
///
/// Variables: p_{i,j} means pigeon i is in hole j.
/// - For each pigeon i: at least one hole (OR_j p_{i,j})
/// - For each hole j and distinct pigeons i,k: at most one pigeon (NOT p_{i,j} OR NOT p_{k,j})
///
/// This formula is UNSATISFIABLE (n+1 pigeons can't fit in n holes).
///
/// **Proof complexity:**
/// - Resolution: exponential (2^{Omega(n)}) - Haken 1985
/// - Extended Resolution: polynomial O(n^3) - Cook 1976
///
/// # Arguments
/// * `n` - Number of holes (pigeons = n + 1)
///
/// # Example
/// ```
/// use ay_proof_complexity::pigeonhole;
///
/// let php3 = pigeonhole(3);  // 4 pigeons, 3 holes
/// // 4 * 3 = 12 variables, many clauses
/// ```
pub fn pigeonhole(n: usize) -> Cnf {
    if n == 0 {
        // 1 pigeon, 0 holes: empty clause makes this UNSAT.
        let mut cnf = Cnf::new_with_capacity(1, 1);
        cnf.add_clause(&[]);
        return cnf;
    }
    let pigeons = n + 1;
    let holes = n;
    // Variable numbering: p_{i,j} -> i * holes + j (0-indexed)
    let var = |pigeon: usize, hole: usize| -> Var { Var::new((pigeon * holes + hole) as u32) };

    // Estimate: pigeons clause count + C(pigeons, 2) * holes
    let clause_count = pigeons + (pigeons * (pigeons - 1) / 2) * holes;
    let mut cnf = Cnf::new_with_capacity((pigeons * holes) as u32, clause_count);

    // At-least-one clauses: each pigeon must be in some hole
    // For each pigeon i: (p_{i,0} OR p_{i,1} OR ... OR p_{i,n-1})
    for pigeon in 0..pigeons {
        let lits: Vec<Lit> = (0..holes)
            .map(|hole| Lit::positive(var(pigeon, hole)))
            .collect();
        cnf.add_clause(&lits);
    }

    // At-most-one clauses: each hole can have at most one pigeon
    // For each hole j and distinct pigeons i,k: (NOT p_{i,j} OR NOT p_{k,j})
    for hole in 0..holes {
        for pigeon1 in 0..pigeons {
            for pigeon2 in (pigeon1 + 1)..pigeons {
                cnf.add_clause(&[
                    Lit::negative(var(pigeon1, hole)),
                    Lit::negative(var(pigeon2, hole)),
                ]);
            }
        }
    }

    cnf
}

/// Generate a random k-CNF formula.
///
/// Each clause has exactly k literals, chosen uniformly at random.
/// The clause-to-variable ratio determines satisfiability:
/// - ratio < ~4.27 (for k=3): likely satisfiable
/// - ratio > ~4.27 (for k=3): likely unsatisfiable
///
/// **Proof complexity:**
/// - Near the threshold, formulas are hard for all known algorithms
///
/// # Arguments
/// * `k` - Clause width (typically 3)
/// * `n` - Number of variables
/// * `m` - Number of clauses
/// * `seed` - Random seed for reproducibility
///
/// # Example
/// ```
/// use ay_proof_complexity::random_k_cnf;
///
/// // Random 3-SAT with 100 variables at threshold ratio
/// let formula = random_k_cnf(3, 100, 427, Some(42));
/// ```
pub fn random_k_cnf(k: usize, n: usize, m: usize, seed: Option<u64>) -> Cnf {
    if n == 0 || k == 0 {
        return Cnf::new_with_capacity(0, 0);
    }

    let mut rng = match seed {
        Some(s) => ChaCha8Rng::seed_from_u64(s),
        None => ChaCha8Rng::from_entropy(),
    };

    let mut cnf = Cnf::new_with_capacity(n as u32, m);

    for _ in 0..m {
        // Sample k distinct variables
        let mut vars: Vec<usize> = (0..n).collect();
        vars.shuffle(&mut rng);
        // Random polarity for each
        let clause: Vec<Lit> = vars
            .into_iter()
            .take(k)
            .map(|v| {
                let var = Var::new(v as u32);
                if rng.gen_bool(0.5) {
                    Lit::positive(var)
                } else {
                    Lit::negative(var)
                }
            })
            .collect();

        cnf.add_clause(&clause);
    }

    cnf
}

/// Generate the parity formula on n variables.
///
/// This encodes: x_1 XOR x_2 XOR ... XOR x_n = 1
///
/// **Proof complexity:**
/// - Resolution: exponential (2^{Omega(n)})
/// - Extended Resolution: polynomial (using auxiliary variables)
///
/// # Arguments
/// * `n` - Number of variables
///
/// # Example
/// ```
/// use ay_proof_complexity::parity;
///
/// let formula = parity(4);  // x1 XOR x2 XOR x3 XOR x4 = 1
/// ```
pub fn parity(n: usize) -> Cnf {
    let vars: Vec<Var> = (0..n).map(|i| Var::new(i as u32)).collect();

    let clause_count = xor_clause_count(n, true);
    let mut cnf = Cnf::new_with_capacity(n as u32, clause_count);
    add_xor_equals_clauses(&vars, true, &mut cnf);

    cnf
}

/// Generate the ordering principle formula (OP).
///
/// The ordering principle states that every finite total order has a minimum element.
/// Variables: p_{i,j} means i < j in the ordering.
///
/// Constraints:
/// - Asymmetry: NOT(p_{i,j}) OR NOT(p_{j,i}) for all i != j
/// - Transitivity: NOT(p_{i,j}) OR NOT(p_{j,k}) OR p_{i,k} for all distinct i,j,k
/// - Totality: p_{i,j} OR p_{j,i} for all i < j
/// - No minimum: for each i, some j with p_{j,i}
///
/// This is UNSATISFIABLE.
///
/// **Proof complexity:**
/// - Resolution: polynomial O(n^4)
/// - However, tree-resolution requires 2^{Omega(n)}
///
/// # Arguments
/// * `n` - Number of elements to order
///
/// # Example
/// ```
/// use ay_proof_complexity::ordering_principle;
///
/// let formula = ordering_principle(4);  // 4 elements with no minimum
/// ```
pub fn ordering_principle(n: usize) -> Cnf {
    if n <= 1 {
        // n=0 or n=1: the "no minimum" constraint can't be satisfied
        let mut cnf = Cnf::new_with_capacity(0, 1);
        cnf.add_clause(&[]); // UNSAT
        return cnf;
    }

    // Variable p_{i,j} for i != j: element i is less than element j
    // Numbering: (i, j) -> i * n + j (but skip diagonal i == j)
    let var = |i: usize, j: usize| -> Var {
        debug_assert_ne!(i, j);
        let idx = i * n + j;
        Var::new(idx as u32)
    };

    // Estimate clauses
    let pairs = n * (n - 1);
    let triples = n * (n - 1) * (n - 2);
    let clause_count = pairs / 2 + pairs + triples + n;

    let mut cnf = Cnf::new_with_capacity((n * n) as u32, clause_count);

    // Asymmetry: NOT(p_{i,j}) OR NOT(p_{j,i})
    for i in 0..n {
        for j in 0..n {
            if i < j {
                cnf.add_clause(&[Lit::negative(var(i, j)), Lit::negative(var(j, i))]);
            }
        }
    }

    // Totality: p_{i,j} OR p_{j,i}
    for i in 0..n {
        for j in (i + 1)..n {
            cnf.add_clause(&[Lit::positive(var(i, j)), Lit::positive(var(j, i))]);
        }
    }

    // Transitivity: NOT(p_{i,j}) OR NOT(p_{j,k}) OR p_{i,k}
    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            for k in 0..n {
                if k == i || k == j {
                    continue;
                }
                cnf.add_clause(&[
                    Lit::negative(var(i, j)),
                    Lit::negative(var(j, k)),
                    Lit::positive(var(i, k)),
                ]);
            }
        }
    }

    // No minimum: for each i, there exists j such that j < i
    // This is: OR_{j != i} p_{j,i}
    for i in 0..n {
        let clause: Vec<Lit> = (0..n)
            .filter(|&j| j != i)
            .map(|j| Lit::positive(var(j, i)))
            .collect();
        cnf.add_clause(&clause);
    }

    cnf
}

#[cfg(test)]
#[path = "hard_formulas_tests.rs"]
mod tests;
