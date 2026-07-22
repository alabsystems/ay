// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
//! Soundness validator for the ECgrid cnf equality-recovery path.
//!
//! For each OPB file argument, prints:
//!   native_unsat  : `gf2_parity_detects_unsat` on the original `=` rows only.
//!   recov_count   : number of entailed equalities recovered.
//!   recov_unsat   : `gf2_parity_detects_unsat_with_recovery`.
//!   indep_entailed: every recovered equality independently re-certified as a
//!                   nonnegative integer combination of present `>=` rows
//!                   (this code re-derives the floor/ceil bounds from scratch,
//!                   a SEPARATE implementation from the solver's).
//!   brute (only when <= 16 vars): exhaustively confirm every original-feasible
//!                   0/1 point satisfies every recovered equality (true
//!                   entailment) — and, if recov_unsat, confirm the instance has
//!                   NO feasible point (the UNSAT is real).
//!
//! A line is FLAGGED if recov_unsat but the instance is actually satisfiable, or
//! if any recovered equality fails independent re-certification / brute-force
//! entailment.

use ay_pb::{
    debug_recovered_equalities, gf2_parity_detects_unsat, gf2_parity_detects_unsat_with_recovery,
    parse_opb, PbConstraint, PbRel,
};
use std::collections::HashMap;

/// Independently re-certify `sum_S = k` is entailed by the present `±1` `Ge`
/// rows: re-derive the floor (from at-least rows whose support ⊆ S, summed) and
/// the ceil (from at-most rows ⊆ S, summed) with uniform-coefficient checks.
fn independently_entailed(constraints: &[PbConstraint], eq: &PbConstraint) -> bool {
    let set: Vec<u32> = eq.terms.iter().map(|t| t.lits[0].var).collect();
    let set_lookup: std::collections::HashSet<u32> = set.iter().copied().collect();
    let k = eq.rhs;

    let mut lo_c: HashMap<u32, i128> = HashMap::new();
    let mut lo_r: i128 = 0;
    let mut lo_n = 0usize;
    let mut hi_c: HashMap<u32, i128> = HashMap::new();
    let mut hi_r: i128 = 0;
    let mut hi_n = 0usize;

    for c in constraints {
        if c.rel != PbRel::Ge || c.terms.is_empty() {
            continue;
        }
        // Distill ±1 plain cardinality row.
        let mut vars = Vec::new();
        let mut sign: Option<i128> = None;
        let mut ok = true;
        for term in &c.terms {
            if term.lits.len() != 1 || term.lits[0].negated {
                ok = false;
                break;
            }
            let s = term.coeff;
            if s != 1 && s != -1 {
                ok = false;
                break;
            }
            match sign {
                None => sign = Some(s),
                Some(p) if p == s => {}
                _ => {
                    ok = false;
                    break;
                }
            }
            vars.push(term.lits[0].var);
        }
        if !ok {
            continue;
        }
        if !vars.iter().all(|v| set_lookup.contains(v)) {
            continue;
        }
        if sign == Some(1) {
            for v in &vars {
                *lo_c.entry(*v).or_default() += 1;
            }
            lo_r += c.rhs;
            lo_n += 1;
        } else {
            for v in &vars {
                *hi_c.entry(*v).or_default() += 1;
            }
            hi_r += c.rhs;
            hi_n += 1;
        }
    }

    let uniform = |m: &HashMap<u32, i128>, n: usize| -> Option<i128> {
        if n == 0 {
            return None;
        }
        let first = *m.get(&set[0])?;
        if first <= 0 {
            return None;
        }
        for v in &set {
            if *m.get(v)? != first {
                return None;
            }
        }
        Some(first)
    };

    let lo = match uniform(&lo_c, lo_n) {
        Some(c) => {
            // sum >= ceil(lo_r / c)
            let q = lo_r.div_euclid(c);
            let r = lo_r.rem_euclid(c);
            if r == 0 {
                q
            } else {
                q + 1
            }
        }
        None => return false,
    };
    let hi = match uniform(&hi_c, hi_n) {
        Some(c) => (-hi_r).div_euclid(c), // floor(-hi_r / c)
        None => return false,
    };
    lo == hi && lo == k
}

fn lit_val(c: &PbConstraint, idx: usize, x: u64) -> bool {
    let l = c.terms[idx].lits[0];
    let bit = (x >> (l.var - 1)) & 1 == 1;
    if l.negated {
        !bit
    } else {
        bit
    }
}

fn holds(c: &PbConstraint, x: u64) -> bool {
    let mut lhs = 0i128;
    for i in 0..c.terms.len() {
        if lit_val(c, i, x) {
            lhs += c.terms[i].coeff;
        }
    }
    match c.rel {
        PbRel::Ge => lhs >= c.rhs,
        PbRel::Eq => lhs == c.rhs,
        _ => true,
    }
}

fn main() {
    let mut any_flag = false;
    println!(
        "{:<48} {:>6} {:>6} {:>6} {:>8} {:>10}",
        "instance", "natUN", "#recov", "recUN", "indepOK", "brute"
    );
    for path in std::env::args().skip(1) {
        let src = match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                println!("{path}: read error {e}");
                continue;
            }
        };
        let inst = match parse_opb(&src) {
            Ok(i) => i,
            Err(e) => {
                println!("{path}: parse error {e:?}");
                continue;
            }
        };
        let name = std::path::Path::new(&path)
            .file_name()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or(path.clone());

        let native = gf2_parity_detects_unsat(&inst.constraints, inst.num_vars);
        let recovered = debug_recovered_equalities(&inst.constraints, inst.num_vars);
        let recov_unsat = gf2_parity_detects_unsat_with_recovery(&inst.constraints, inst.num_vars);

        let indep_ok = recovered
            .iter()
            .all(|eq| independently_entailed(&inst.constraints, eq));

        let mut brute = String::from("skip");
        if inst.num_vars <= 16 {
            let n = inst.num_vars;
            let mut feasible_exists = false;
            let mut entail_ok = true;
            for x in 0u64..(1u64 << n) {
                if inst.constraints.iter().all(|c| holds(c, x)) {
                    feasible_exists = true;
                    if !recovered.iter().all(|eq| holds(eq, x)) {
                        entail_ok = false;
                        break;
                    }
                }
            }
            if !entail_ok {
                brute = String::from("ENTAIL-FAIL");
                any_flag = true;
            } else if recov_unsat && feasible_exists {
                brute = String::from("FALSE-UNSAT");
                any_flag = true;
            } else {
                brute = format!("ok(sat={feasible_exists})");
            }
        }

        if !indep_ok && (recov_unsat || !recovered.is_empty()) {
            any_flag = true;
        }

        println!(
            "{:<48} {:>6} {:>6} {:>6} {:>8} {:>10}",
            &name[..name.len().min(48)],
            native,
            recovered.len(),
            recov_unsat,
            indep_ok,
            brute
        );
        use std::io::Write;
        let _ = std::io::stdout().flush();
    }
    if any_flag {
        eprintln!("!!! SOUNDNESS FLAG RAISED — see FALSE-UNSAT / ENTAIL-FAIL / indepOK=false");
        std::process::exit(1);
    } else {
        eprintln!("OK: no soundness flags");
    }
}
