// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inputs that exhaust a `--memory` budget deterministically, for the
//! memout-grammar tests in the parent module.

/// A QF_UF instance whose two `distinct` blocks over 2500 constants expand to
/// ~6M disequalities: it breaches a 64 MiB `--memory` budget in well under a
/// second on every posture (measured 0.08 s), so it is a deterministic memout.
pub(super) fn memory_hungry_smt() -> String {
    let n = 2500;
    let mut script = String::from("(set-logic QF_UF)\n(declare-sort U 0)\n");
    for i in 0..n {
        script.push_str(&format!("(declare-const a{i} U)\n"));
    }
    script.push_str("(declare-fun g (U) U)\n(assert (distinct");
    for i in 0..n {
        script.push_str(&format!(" a{i}"));
    }
    script.push_str("))\n(assert (distinct");
    for i in 0..n {
        script.push_str(&format!(" (g a{i})"));
    }
    script.push_str("))\n");
    for i in 0..n - 1 {
        script.push_str(&format!(
            "(assert (or (= (g a{i}) a{}) (= (g a{}) a{i})))\n",
            i + 1,
            i + 1
        ));
    }
    script.push_str("(check-sat)\n");
    script
}

/// Bytes of DIMACS text [`memory_hungry_cnf`] produces at least: twice a
/// 1 MiB budget.
pub(super) const MEMORY_HUNGRY_CNF_MIN_BYTES: usize = 2 * 1024 * 1024;

/// An unsatisfiable implication chain, `1`, `-i i+1` for every `i` up to
/// 150 000, then `-150001`, whose text is over [`MEMORY_HUNGRY_CNF_MIN_BYTES`]
/// (2.3 MB).
///
/// Its memout is forced, not raced: both DIMACS routes read the whole file in
/// one heap allocation after the ceiling is armed (`read_to_string` in
/// `run::run_file` on the fast route, `read_to_end` in
/// `dimacs::run_dimacs_proof_from_file` on the proof route), so a 1 MiB budget
/// is refused by the allocator's hard ceiling on the reading thread before one
/// clause is parsed, whenever the memory watchdog thread runs. The contradiction
/// needs the last clause, and without a budget both postures answer
/// `s UNSATISFIABLE` (z3 4.8.12 agrees; measured 2026-10-07).
pub(super) fn memory_hungry_cnf() -> String {
    const CHAIN: usize = 150_000;
    let mut cnf = format!("p cnf {} {}\n1 0\n", CHAIN + 1, CHAIN + 2);
    for i in 1..=CHAIN {
        cnf.push_str(&format!("-{i} {} 0\n", i + 1));
    }
    cnf.push_str(&format!("-{} 0\n", CHAIN + 1));
    cnf
}
