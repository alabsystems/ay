// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Repeat one IDENTICAL query N times in ONE process and print the VERDICT
//! sequence.
//!
//! Built to answer a single question: can state carried between solves in one
//! process make solve `N` answer differently from solve 1 on byte-identical
//! input? Diagnostics-only counters are deliberately NOT the subject — only
//! verdicts and the SEARCH counters that gate them, because only those are the
//! contract.
//!
//! Usage:
//!   verdict_determinism_probe [ITERATIONS] [MODE] [TIMEOUT_MS] [MEMORY_MB] [FILE]
//!
//! MODE:
//!   pushpop  one `Solver`, `push`/assert/`check_sat`/`pop` per iteration
//!   fresh    a brand-new `Solver` per iteration, same process
//!   file     parse FILE once, then run it through a brand-new `Executor` per
//!            iteration, same process (the long-lived-host shape)
//!
//! Run with ITERATIONS=1 from a shell loop to get the N-fresh-processes
//! control.
//!
//! The built-in query is the one measured drifting in deductive-checks (`Unsat` on one
//! call, `Unknown` on the next):
//!
//! ```smt2
//! (declare-const len_v_pre Int)
//! (assert (and (<= 0 len_v_pre) (<= len_v_pre 18446744073709551614)))
//! (assert (not (and (<= 0 (+ len_v_pre 1))
//!                   (<= (+ len_v_pre 1) 18446744073709551615))))
//! ```

use std::time::Duration;

use ay_dpll::api::{Logic, SolveResult, Solver, Sort};
use num_bigint::BigInt;

/// The search counters a verdict actually depends on. Excludes every
/// wall-clock and every process-global diagnostic counter.
#[derive(Debug, Clone, PartialEq, Eq)]
struct SearchCounters {
    conflicts: u64,
    decisions: u64,
    propagations: u64,
    restarts: u64,
    theory_conflicts: u64,
    theory_propagations: u64,
    theory_unknown_count: u64,
}

impl SearchCounters {
    fn of(statistics: &ay_dpll::Statistics) -> Self {
        Self {
            conflicts: statistics.conflicts,
            decisions: statistics.decisions,
            propagations: statistics.propagations,
            restarts: statistics.restarts,
            theory_conflicts: statistics.theory_conflicts,
            theory_propagations: statistics.theory_propagations,
            theory_unknown_count: statistics.theory_unknown_count,
        }
    }

    fn render(&self) -> String {
        format!(
            "conf={} dec={} prop={} rest={} tconf={} tprop={} tunk={}",
            self.conflicts,
            self.decisions,
            self.propagations,
            self.restarts,
            self.theory_conflicts,
            self.theory_propagations,
            self.theory_unknown_count,
        )
    }
}

fn build_query(solver: &mut Solver) {
    let len = solver.declare_const("len_v_pre", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let u64_max = solver.int_const_bigint(&BigInt::from(u64::MAX));
    let u64_max_minus_one = solver.int_const_bigint(&(BigInt::from(u64::MAX) - BigInt::from(1u32)));

    // Premises: len_v_pre is a well-formed u64 length with room to grow.
    let lo = solver.try_le(zero, len).expect("integer comparison");
    let hi = solver
        .try_le(len, u64_max_minus_one)
        .expect("integer comparison");
    solver.try_assert_term(lo).expect("Boolean assertion");
    solver.try_assert_term(hi).expect("Boolean assertion");

    // Negated goal: the post-push length is NOT in u64 range.
    let next = solver.try_add(len, one).expect("integer addition");
    let goal_lo = solver.try_le(zero, next).expect("integer comparison");
    let goal_hi = solver.try_le(next, u64_max).expect("integer comparison");
    let goal = solver.try_and(goal_lo, goal_hi).expect("conjunction");
    let negated = solver.try_not(goal).expect("negation");
    solver.try_assert_term(negated).expect("Boolean assertion");
}

fn configure(solver: &mut Solver, timeout_ms: u64, memory_mb: usize) {
    if timeout_ms > 0 {
        solver.set_timeout(Some(Duration::from_millis(timeout_ms)));
    }
    if memory_mb > 0 {
        solver.set_memory_limit(Some(memory_mb * 1024 * 1024));
    }
}

fn verdict_label(result: &SolveResult, reason: Option<String>) -> String {
    match result {
        SolveResult::Sat => "Sat".to_string(),
        SolveResult::Unsat(_) => "Unsat".to_string(),
        SolveResult::Unknown => match reason {
            Some(reason) => format!("Unknown({reason})"),
            None => "Unknown".to_string(),
        },
        other => format!("{other:?}"),
    }
}

struct Round {
    verdict: String,
    counters: SearchCounters,
    millis: u128,
    extra: String,
}

/// Render the `Statistics.extra` keys that name a REFUSAL, so an `Unknown`
/// round can be diffed against an `Unsat` round of the identical query.
fn refusal_extras(statistics: &ay_dpll::Statistics) -> String {
    let mut out: Vec<String> = Vec::new();
    for (key, value) in &statistics.extra {
        let interesting = key.starts_with("unknown.")
            || key.starts_with("proof_")
            || key.contains("reject")
            || key.contains("refus")
            || key.contains("cancel")
            || key.contains("resource")
            || key.contains("strict");
        if interesting {
            out.push(format!("{key}={value:?}"));
        }
    }
    out.join(" ")
}

fn main() {
    let mut args = std::env::args().skip(1);
    let iterations: usize = args.next().and_then(|a| a.parse().ok()).unwrap_or(20);
    let mode = args.next().unwrap_or_else(|| "pushpop".to_string());
    let timeout_ms: u64 = args.next().and_then(|a| a.parse().ok()).unwrap_or(30_000);
    let memory_mb: usize = args.next().and_then(|a| a.parse().ok()).unwrap_or(0);
    let file = args.next();

    let mut rounds: Vec<Round> = Vec::with_capacity(iterations);

    match mode.as_str() {
        "pushpop" => {
            let mut solver = Solver::try_new(Logic::All).expect("ALL is supported");
            configure(&mut solver, timeout_ms, memory_mb);
            for _ in 0..iterations {
                solver.push();
                build_query(&mut solver);
                let started = std::time::Instant::now();
                let details = solver.check_sat_with_details();
                rounds.push(Round {
                    verdict: verdict_label(
                        details.result.result(),
                        details.unknown_reason.map(|r| format!("{r:?}")),
                    ),
                    counters: SearchCounters::of(&details.statistics),
                    millis: started.elapsed().as_millis(),
                    extra: refusal_extras(&details.statistics),
                });
                solver.pop();
            }
        }
        "fresh" => {
            for _ in 0..iterations {
                let mut solver = Solver::try_new(Logic::All).expect("ALL is supported");
                configure(&mut solver, timeout_ms, memory_mb);
                build_query(&mut solver);
                let started = std::time::Instant::now();
                let details = solver.check_sat_with_details();
                rounds.push(Round {
                    verdict: verdict_label(
                        details.result.result(),
                        details.unknown_reason.map(|r| format!("{r:?}")),
                    ),
                    counters: SearchCounters::of(&details.statistics),
                    millis: started.elapsed().as_millis(),
                    extra: refusal_extras(&details.statistics),
                });
            }
        }
        "file" => {
            let path = file.clone().expect("mode `file` needs a FILE argument");
            let input = std::fs::read_to_string(&path).expect("readable SMT-LIB2 file");
            let commands = ay_frontend::parse(&input).expect("parseable SMT-LIB2 file");
            for _ in 0..iterations {
                let mut executor = ay_dpll::Executor::new();
                let started = std::time::Instant::now();
                let mut answers: Vec<String> = Vec::new();
                for command in &commands {
                    match executor.execute(command) {
                        Ok(Some(output)) => {
                            if matches!(output.as_str(), "sat" | "unsat" | "unknown") {
                                answers.push(output);
                            }
                        }
                        Ok(None) => {}
                        Err(error) => {
                            answers.push(format!("error:{error:?}"));
                            break;
                        }
                    }
                }
                rounds.push(Round {
                    verdict: answers.join(","),
                    counters: SearchCounters::of(executor.statistics()),
                    millis: started.elapsed().as_millis(),
                    extra: refusal_extras(executor.statistics()),
                });
            }
        }
        other => {
            eprintln!("unknown mode {other:?}; expected `pushpop`, `fresh` or `file`");
            std::process::exit(2);
        }
    }

    println!("TESTS_RAN {}", rounds.len());
    println!(
        "MODE {mode} TIMEOUT_MS {timeout_ms} MEMORY_MB {memory_mb} FILE {}",
        file.as_deref().unwrap_or("-")
    );
    for (i, round) in rounds.iter().enumerate() {
        println!(
            "  solve {i:>3}: {:<28} {:>7}ms  {}",
            round.verdict,
            round.millis,
            round.counters.render()
        );
        if !round.extra.is_empty() {
            println!("             extra: {}", round.extra);
        }
    }
    let distinct_verdicts: std::collections::BTreeSet<&String> =
        rounds.iter().map(|r| &r.verdict).collect();
    let counter_drift = rounds.iter().any(|r| r.counters != rounds[0].counters);
    println!("DISTINCT_VERDICTS {}", distinct_verdicts.len());
    println!(
        "VERDICT_DRIFT {}",
        if distinct_verdicts.len() > 1 {
            "yes"
        } else {
            "no"
        }
    );
    println!(
        "SEARCH_COUNTER_DRIFT {}",
        if counter_drift { "yes" } else { "no" }
    );
    if distinct_verdicts.len() > 1 {
        std::process::exit(1);
    }
}
