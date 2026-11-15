use std::time::Instant;

use clap::Parser;
use veripb_formula::prelude::PBConstraint;
use veripb_parser::cnf_parser::parse_cnf_from_file;

#[derive(Parser)]
struct Settings {
    path: std::path::PathBuf,
}

fn main() {
    let args = Settings::parse();

    let start = Instant::now();
    let (formula, num_vars) = match parse_cnf_from_file(args.path) {
        Ok(output) => output,
        Err(e) => {
            eprintln!("{e}");
            return;
        }
    };
    let duration = start.elapsed();
    println!("Parsing time: {}s", duration.as_secs_f64());

    let mut total_num_lits = 0;
    for clause in formula.constraints.iter() {
        total_num_lits += clause.len();
    }

    println!("The DIMACS CNF file has the following statistics:");
    println!("#Clauses: {}", formula.len());
    println!("#Vars: {num_vars}");
    println!(
        "avg. lits/clause: {}",
        total_num_lits as f64 / formula.len() as f64
    )
}
