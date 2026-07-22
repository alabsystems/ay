// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof-materialization overhead measurement for the route-b UNSAT
//! certificate channel (Program CK1 WS1-M1 deliverable, ledger target <= 5%
//! on the lowering-miter workload).
//!
//! This is an integration test on purpose: unit tests compile the library
//! with `cfg(test)`, which activates the internal debug-only LRAT chain
//! checker inside the proof manager and inflates the measurement by orders of
//! magnitude (the same holds for `debug_assertions` builds). The ledger
//! number therefore comes from:
//!
//! ```text
//! cargo test -p ay-sat --release --features unsat-cert \
//!     --test unsat_cert_overhead -- --nocapture --test-threads=1
//! ```
//!
//! Two workloads, measured separately because their physics differ:
//!
//! * **Lowering miter** (the actual route-b workload, the shape of external-codegen's
//!   t-silicon rule certificates): propagation-dominated, small refutations —
//!   LRAT materialization is noise-level (~0–2% in release).
//! * **Pigeonhole** (adversarial control): resolution-pathological, so the
//!   LRAT certificate itself is enormous (~10 MB for PHP(9,8), ~120x the DRAT
//!   bytes) and materialization cost is dominated by the certificate size,
//!   not by a fixable inefficiency. Reported for honesty, not gated.

#![cfg(feature = "unsat-cert")]

use ay_sat::{prove_cnf_unsat_dimacs, Literal, ProofOutput, SatResult, Solver};
use std::time::{Duration, Instant};

/// Pigeonhole CNF PHP(pigeons, holes): UNSAT whenever pigeons > holes.
fn php_cnf(pigeons: usize, holes: usize) -> (usize, Vec<Vec<i32>>) {
    let var = |p: usize, h: usize| -> i32 { (p * holes + h + 1) as i32 };
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    for p in 0..pigeons {
        clauses.push((0..holes).map(|h| var(p, h)).collect());
    }
    for h in 0..holes {
        for p1 in 0..pigeons {
            for p2 in (p1 + 1)..pigeons {
                clauses.push(vec![-var(p1, h), -var(p2, h)]);
            }
        }
    }
    (pigeons * holes, clauses)
}

/// A `width`-bit adder self-miter in the shape of external-codegen's t-silicon
/// fixtures: two structurally distinct Tseitin ripple-carry encodings of
/// `a + b`, XOR-mitred, asserting some output bit differs — UNSAT because the
/// encodings agree on every input. Built inline so the test stays hermetic
/// (external-codegen's fixture files are not read from this repo).
fn adder_miter(width: usize) -> (usize, Vec<Vec<i32>>) {
    let mut next = 0i32;
    let mut fresh = || {
        next += 1;
        next
    };
    let a: Vec<i32> = (0..width).map(|_| fresh()).collect();
    let b: Vec<i32> = (0..width).map(|_| fresh()).collect();
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    // o = x ^ y ^ z (Tseitin: forbid each violating assignment).
    let xor3 = |x: i32, y: i32, z: i32, clauses: &mut Vec<Vec<i32>>, o: i32| {
        for mask in 0..8 {
            let (sx, sy, sz) = (mask & 1 != 0, mask & 2 != 0, mask & 4 != 0);
            let so = sx ^ sy ^ sz;
            clauses.push(vec![
                if sx { -x } else { x },
                if sy { -y } else { y },
                if sz { -z } else { z },
                if so { o } else { -o },
            ]);
        }
    };
    // c = MAJ(x, y, z).
    let maj = |x: i32, y: i32, z: i32, clauses: &mut Vec<Vec<i32>>, c: i32| {
        clauses.push(vec![-x, -y, c]);
        clauses.push(vec![-x, -z, c]);
        clauses.push(vec![-y, -z, c]);
        clauses.push(vec![x, y, -c]);
        clauses.push(vec![x, z, -c]);
        clauses.push(vec![y, z, -c]);
    };
    // Two independent ripple-carry chains for a + b.
    let mut sums: [Vec<i32>; 2] = [Vec::new(), Vec::new()];
    for side in 0..2 {
        let mut carry: Option<i32> = None;
        for i in 0..width {
            let s = fresh();
            match carry {
                None => {
                    // Bit 0: model the zero carry-in as a fresh false var so
                    // the two sides share no gate variables.
                    let f = fresh();
                    clauses.push(vec![-f]);
                    xor3(a[i], b[i], f, &mut clauses, s);
                    if i + 1 < width {
                        let c = fresh();
                        maj(a[i], b[i], f, &mut clauses, c);
                        carry = Some(c);
                    }
                }
                Some(cin) => {
                    xor3(a[i], b[i], cin, &mut clauses, s);
                    if i + 1 < width {
                        let c = fresh();
                        maj(a[i], b[i], cin, &mut clauses, c);
                        carry = Some(c);
                    }
                }
            }
            sums[side].push(s);
        }
    }
    // Miter outputs: d_i = sum0_i ^ sum1_i; assert at least one differs.
    let diffs: Vec<i32> = (0..width)
        .map(|i| {
            let d = fresh();
            let (x, y) = (sums[0][i], sums[1][i]);
            clauses.push(vec![-d, x, y]);
            clauses.push(vec![-d, -x, -y]);
            clauses.push(vec![d, -x, y]);
            clauses.push(vec![d, x, -y]);
            d
        })
        .collect();
    clauses.push(diffs);
    (next as usize, clauses)
}

fn to_lits(clauses: &[Vec<i32>]) -> Vec<Vec<Literal>> {
    clauses
        .iter()
        .map(|c| c.iter().map(|&l| Literal::from_dimacs(l)).collect())
        .collect()
}

fn median(mut xs: Vec<Duration>) -> Duration {
    xs.sort();
    xs[xs.len() / 2]
}

/// One solve; when `materialize` is set, LRAT goes to an in-memory buffer —
/// the exact channel `prove_unsat_resolution_dag` rides. Returns elapsed time.
fn solve_once(num_vars: usize, lits: &[Vec<Literal>], materialize: bool) -> Duration {
    let start = Instant::now();
    let mut solver = if materialize {
        Solver::with_proof_output(
            num_vars,
            ProofOutput::lrat_text(Vec::<u8>::new(), lits.len() as u64),
        )
    } else {
        Solver::new(num_vars)
    };
    for c in lits {
        solver.add_clause(c.clone());
    }
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Unsat(_)),
        "workload must be UNSAT"
    );
    if materialize {
        let writer = solver.take_proof_writer().expect("writer present");
        let bytes = writer.into_vec().expect("in-memory flush");
        assert!(!bytes.is_empty(), "materialized proof is non-empty");
    }
    start.elapsed()
}

/// Interleaved off/on medians (interleaving cancels machine drift); returns
/// the overhead percentage of on over off.
fn measure_overhead_pct(num_vars: usize, lits: &[Vec<Literal>], reps: usize) -> (f64, Duration) {
    for _ in 0..2 {
        solve_once(num_vars, lits, false);
        solve_once(num_vars, lits, true);
    }
    let mut off = Vec::with_capacity(reps);
    let mut on = Vec::with_capacity(reps);
    for _ in 0..reps {
        off.push(solve_once(num_vars, lits, false));
        on.push(solve_once(num_vars, lits, true));
    }
    let (off, on) = (median(off), median(on));
    let pct = (on.as_secs_f64() - off.as_secs_f64()) / off.as_secs_f64() * 100.0;
    (pct, off)
}

/// The route-b workload number: proof materialization on vs off for a 32-bit
/// lowering-style miter. Ledger target <= 5% (release); the in-test assertion
/// is deliberately loose so debug/CI timing noise cannot flake it.
#[test]
fn proof_materialization_overhead_lowering_miter() {
    let (num_vars, clauses) = adder_miter(32);
    let lits = to_lits(&clauses);
    let (pct, base) = measure_overhead_pct(num_vars, &lits, 15);
    println!(
        "proof-materialization overhead, adder_miter(32): base={base:?} \
         overhead={pct:+.2}% (ledger target <= 5% in release)"
    );
    assert!(
        pct < 100.0,
        "miter materialization overhead {pct:.2}% is out of sanity range"
    );
}

/// Adversarial control: pigeonhole refutations are resolution-pathological,
/// so the LRAT certificate is huge (~10 MB text for PHP(9,8), ~120x DRAT) and
/// materialization cost tracks certificate size. Informational — printed for
/// the ledger's honesty row, not gated (no <=5% claim is made or makeable for
/// this shape; DRAT-by-default stays ~0.5% here).
#[test]
fn proof_materialization_overhead_pigeonhole_adversarial() {
    let (num_vars, clauses) = php_cnf(9, 8);
    let lits = to_lits(&clauses);
    let (pct, base) = measure_overhead_pct(num_vars, &lits, 5);
    println!(
        "proof-materialization overhead, PHP(9,8) adversarial control: \
         base={base:?} overhead={pct:+.2}% (informational; certificate-size-bound)"
    );
    assert!(pct.is_finite());
}

/// Full route-b consumption cost on the miter workload: bare verdict solve vs
/// [`prove_cnf_unsat_dimacs`] (solve + in-memory LRAT + parse + RUP-replay
/// validation). This is what external-codegen's ay_bridge pays end to end.
#[test]
fn certificate_export_overhead_lowering_miter() {
    let (num_vars, clauses) = adder_miter(32);
    let lits = to_lits(&clauses);

    let bare = |_: ()| -> Duration {
        let start = Instant::now();
        let mut solver = Solver::new(num_vars);
        for c in &lits {
            solver.add_clause(c.clone());
        }
        assert!(matches!(solver.solve().into_inner(), SatResult::Unsat(_)));
        start.elapsed()
    };
    let export = |_: ()| -> Duration {
        let start = Instant::now();
        let dag = prove_cnf_unsat_dimacs(num_vars, &clauses).expect("UNSAT");
        assert!(dag.derived.last().is_some_and(|s| s.clause.is_empty()));
        start.elapsed()
    };

    for _ in 0..2 {
        bare(());
        export(());
    }
    let reps = 15;
    let mut b = Vec::with_capacity(reps);
    let mut f = Vec::with_capacity(reps);
    for _ in 0..reps {
        b.push(bare(()));
        f.push(export(()));
    }
    let (b, f) = (median(b), median(f));
    let pct = (f.as_secs_f64() - b.as_secs_f64()) / b.as_secs_f64() * 100.0;
    println!(
        "certificate-export overhead, adder_miter(32): bare={b:?} full={f:?} \
         overhead={pct:+.2}% (includes LRAT parse + RUP-replay validation)"
    );
    assert!(pct.is_finite());
}

/// The miter workload's certificate is not just cheap — it round-trips the
/// full validated route-b surface, and the independent `ay-lrat-check`
/// implementation agrees with the internal replay (this also pins the miter
/// generator itself as UNSAT-shaped, guarding the timing tests above).
#[test]
fn miter_certificate_validates_and_cross_checks() {
    use ay_lrat_check::checker::LratChecker;
    use ay_lrat_check::lrat_parser::LratStep;

    let (num_vars, clauses) = adder_miter(8);
    let dag = prove_cnf_unsat_dimacs(num_vars, &clauses).expect("miter is UNSAT");
    dag.validate().expect("miter certificate replays");
    assert_eq!(dag.original_clauses.len(), clauses.len());
    assert!(dag.derived.iter().all(|s| !s.rup_hints.is_empty()));

    let conv = |l: &Literal| ay_lrat_check::dimacs::Literal::from_dimacs(l.to_dimacs());
    let mut checker = LratChecker::new(dag.num_vars);
    for (id, lits) in &dag.original_clauses {
        let lits: Vec<_> = lits.iter().map(conv).collect();
        assert!(checker.add_original(*id, &lits), "original {id} rejected");
    }
    let steps: Vec<LratStep> = dag
        .derived
        .iter()
        .map(|s| LratStep::Add {
            id: s.id,
            clause: s.clause.iter().map(conv).collect(),
            hints: s.rup_hints.iter().map(|&h| h as i64).collect(),
        })
        .collect();
    assert!(
        checker.verify_proof(&steps),
        "independent ay-lrat-check must accept the miter certificate"
    );
}
