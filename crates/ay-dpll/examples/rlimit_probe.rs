//! Does `:rlimit` bound a solve DETERMINISTICALLY, through the API?
//! usage: rlimit_probe <file.smt2> <rlimit|0> <iterations>
use std::io::{self, Write};

fn main() -> Result<(), String> {
    let mut a = std::env::args().skip(1);
    let path = a
        .next()
        .ok_or_else(|| "usage: rlimit_probe <file.smt2> <rlimit|0> <iterations>".to_string())?;
    let budget: u64 = a.next().and_then(|s| s.parse().ok()).unwrap_or(0);
    let iters: usize = a.next().and_then(|s| s.parse().ok()).unwrap_or(3);
    let input = std::fs::read_to_string(&path)
        .map_err(|error| format!("failed to read {path}: {error}"))?;
    let cmds =
        ay_frontend::parse(&input).map_err(|error| format!("failed to parse {path}: {error}"))?;
    let stdout = io::stdout();
    let mut out = stdout.lock();
    writeln!(out, "TESTS_RAN {iters} RLIMIT {budget}").map_err(|error| error.to_string())?;
    for i in 0..iters {
        let mut ex = ay_dpll::Executor::new();
        if budget > 0 {
            // exercise the SAME route a Rust caller has: the option handler.
            let option = format!("(set-option :rlimit {budget})");
            for c in ay_frontend::parse(&option)
                .map_err(|error| format!("failed to parse generated rlimit option: {error}"))?
            {
                ex.execute(&c)
                    .map_err(|error| format!("failed to apply rlimit option: {error}"))?;
            }
        }
        let t = std::time::Instant::now();
        let mut verdict = String::from("(none)");
        for c in &cmds {
            match ex.execute(c) {
                Ok(Some(o)) if matches!(o.as_str(), "sat" | "unsat" | "unknown") => verdict = o,
                Ok(_) => {}
                Err(e) => {
                    verdict = format!("error:{e:?}");
                    break;
                }
            }
        }
        let s = ex.statistics();
        writeln!(
            out,
            "  run {i}: {verdict:>7}  {:>6}ms  conflicts={} rlimit_count={}",
            t.elapsed().as_millis(),
            s.conflicts,
            s.rlimit_count
        )
        .map_err(|error| error.to_string())?;
    }
    Ok(())
}
