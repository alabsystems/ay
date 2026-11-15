use std::time::Instant;

use clap::Parser;
use veripb_formula::prelude::PBConstraint;
use veripb_parser::wcnf_parser::parse_wcnf_from_file;

#[derive(Parser)]
struct Settings {
    path: std::path::PathBuf,
}

fn main() {
    let args = Settings::parse();

    let start = Instant::now();
    let (formula, var_names) = match parse_wcnf_from_file(args.path) {
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

    println!("The WCNF file has the following statistics:");
    println!("#Constraints: {}", formula.len());
    println!("#Vars: {}", var_names.len());
    println!(
        "avg. lits / hard clause: {}",
        total_num_lits as f64 / formula.len() as f64
    )
}
