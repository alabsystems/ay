// Preprocessing measurement harness (PB preprocessing strengthening work).
//
// Parses one OPB instance and runs BOTH preprocessing pipelines with a wall
// timer, reporting rows/vars before/after plus per-pass counters — one
// machine-readable line per pipeline per instance so a shell loop can build a
// table:
//   PP   <name> ...  — default pipeline (entailed-only; what PbCdclSolver::new runs)
//   PPOS <name> ...  — one-shot pipeline (adds choice reductions / pure literals)
//
// Usage: cargo run --release --example preprocess_stats -- <file.opb>...

use std::collections::BTreeSet;
use std::time::Instant;

use ay_pb::preprocess::{
    preprocess_one_shot, preprocess_with_stats, PreprocessResult, PreprocessStats,
};
use ay_pb::{parse_opb, PbInstance};

fn used_vars(instance: &PbInstance) -> usize {
    let mut vars: BTreeSet<u32> = BTreeSet::new();
    for c in &instance.constraints {
        for t in &c.terms {
            for l in &t.lits {
                vars.insert(l.var);
            }
        }
    }
    vars.len()
}

fn report(
    tag: &str,
    name: &str,
    rows_in: usize,
    vars_in: usize,
    result: &PreprocessResult,
    stats: &PreprocessStats,
    wall_ms: f64,
) {
    match result {
        PreprocessResult::Simplified {
            instance: out,
            fixed_literals,
        } => {
            println!(
                "{tag} {name} verdict=simplified rows_in={rows_in} rows_out={} vars_in={vars_in} vars_used_out={} fixed={} dom_card={} dom_wt={} pure={} residue={} wall_ms={wall_ms:.1}",
                out.constraints.len(),
                used_vars(out),
                fixed_literals.len(),
                stats.dominated_cardinality,
                stats.dominated_weighted,
                stats.pure_fixed,
                stats.gcd_residue_strengthened,
            );
        }
        PreprocessResult::Unsatisfiable => {
            println!(
                "{tag} {name} verdict=unsat rows_in={rows_in} rows_out=0 vars_in={vars_in} vars_used_out=0 fixed=0 wall_ms={wall_ms:.1}"
            );
        }
        PreprocessResult::Interrupted => {
            println!(
                "{tag} {name} verdict=interrupted rows_in={rows_in} rows_out={rows_in} vars_in={vars_in} vars_used_out={vars_in} fixed=0 wall_ms={wall_ms:.1}"
            );
        }
        _ => println!("{tag} {name} verdict=other wall_ms={wall_ms:.1}"),
    }
}

fn main() {
    for path in std::env::args().skip(1) {
        let text = std::fs::read_to_string(&path).expect("failed to read instance");
        let instance = match parse_opb(&text) {
            Ok(i) => i,
            Err(e) => {
                eprintln!("PP {path} parse-error: {e:?}");
                continue;
            }
        };
        let rows_in = instance.constraints.len();
        let vars_in = used_vars(&instance);
        let name = path.rsplit('/').next().unwrap_or(&path).to_string();

        let start = Instant::now();
        let (result, stats) = preprocess_with_stats(&instance);
        let wall_ms = start.elapsed().as_secs_f64() * 1000.0;
        report("PP", &name, rows_in, vars_in, &result, &stats, wall_ms);

        let start = Instant::now();
        let (result, stats) = preprocess_one_shot(&instance);
        let wall_ms = start.elapsed().as_secs_f64() * 1000.0;
        report("PPOS", &name, rows_in, vars_in, &result, &stats, wall_ms);
    }
}
