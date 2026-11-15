// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Random 3-SAT from a 64-bit LCG, identical on every platform, for CLI tests
//! that need a formula of a known size and hardness.

/// `clauses` random 3-literal clauses over `variables` variables, drawn from
/// a 64-bit LCG seeded with `seed`: DIMACS text.
pub(crate) fn random_3sat(variables: u64, clauses: usize, seed: u64) -> String {
    let mut state = seed;
    let mut text = format!("p cnf {variables} {clauses}\n");
    for _ in 0..clauses {
        let mut literals: Vec<i64> = Vec::with_capacity(3);
        while literals.len() < 3 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let variable = i64::try_from((state >> 33) % variables + 1).expect("small variable");
            if literals.iter().all(|literal| literal.abs() != variable) {
                literals.push(if (state >> 32) & 1 == 1 {
                    variable
                } else {
                    -variable
                });
            }
        }
        text.push_str(&format!(
            "{} {} {} 0\n",
            literals[0], literals[1], literals[2]
        ));
    }
    text
}
