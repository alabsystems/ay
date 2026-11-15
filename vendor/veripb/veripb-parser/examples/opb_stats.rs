use std::time::Instant;

use clap::Parser;
use veripb_parser::opb_parser::parse_opb_from_file;

#[derive(Parser)]
struct Settings {
    path: std::path::PathBuf,
}

fn main() {
    let args = Settings::parse();

    let start = Instant::now();
    let (formula, var_names, _, _) = match parse_opb_from_file(args.path) {
        Ok(output) => output,
        Err(e) => {
            eprintln!("{e}");
            return;
        }
    };
    let duration = start.elapsed();

    println!("The OPB file has the following statistics:");
    println!("#Constraints: {}", formula.len());
    println!("#Vars: {}", var_names.len());
    println!("Parsing time: {}s", duration.as_secs_f64());
}
