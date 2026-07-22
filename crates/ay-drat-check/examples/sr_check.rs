// Copyright 2026 Andrew Yates
// Standalone driver for the native PR/SR checker (verification harness).
// Usage: sr_check <cnf> <proof>

use ay_drat_check::cnf_parser::parse_cnf;
use ay_drat_check::drat_parser::parse_drat;
use ay_drat_check::SrChecker;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("Usage: {} <cnf> <proof>", args[0]);
        std::process::exit(2);
    }
    let cnf_bytes = std::fs::read(&args[1]).expect("read cnf");
    let proof_bytes = std::fs::read(&args[2]).expect("read proof");
    let cnf = parse_cnf(&cnf_bytes[..]).expect("parse cnf");
    let steps = parse_drat(&proof_bytes).expect("parse proof");
    let mut chk = SrChecker::new(cnf.num_vars, true);
    match chk.verify(&cnf.clauses, &steps) {
        Ok(()) => {
            println!("s VERIFIED");
            std::process::exit(0);
        }
        Err(e) => {
            println!("s NOT VERIFIED");
            eprintln!("c {e}");
            std::process::exit(1);
        }
    }
}
