// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One proof-grade PDR run and its metered work, on a host the slow-host seam
//! can make slower (the development design notes §13, the clock-steering
//! census of P4a slice 7; §14, the slow-host gate of slice 8's effort).
//!
//! ```text
//! chc_proof_work FILE [--timeout-ms=N] [--effort=B] [--token] [--threads=K]
//!                     [--charge-delay-ns=N] [--tick-delay-ps=N] [--stop-poll-delay-ns=N]
//! ```
//!
//! Runs `engines::solve_pdr_proof` on FILE with model-checker-consumer's production profile
//! (`PdrConfig::production(false)`, the solve timeout N ms, default 5000: what
//! `ay_encode::EncodeConfig::to_pdr_config` builds), with the tick budget B if
//! `--effort` gives one (the timeout is then its backstop), and prints one
//! JSON line: the result, the digests of the run's metadata and model
//! artifact, the wall time, the meter charges and SAT stop polls the run
//! made, and its work (`ChcPdrProofRun::work`). `--token` gives the run a
//! cancellation token nobody cancels (an embedder's, as
//! `solve_with_proof_with_cancellation` passes). `--threads=K` runs K copies at
//! once in this process and prints each one's line in a JSON array, the first
//! thread first.
//!
//! The slow-host seams make a clock read in the run see a slower host while
//! every count stays the same:
//!
//! * `--charge-delay-ns=N` sleeps N ns inside every meter charge with no
//!   effort (`test_seams::delay_each_charge`, the census's slow host). To run a
//!   file on a host K times slower, run it once with no delay and give the
//!   second run `(K - 1) * wall_ns / charges`.
//! * `--tick-delay-ps=N` sleeps N ps for every tick a node is charged, scaled
//!   by the charge's cost (`test_seams::delay_each_tick_picos`, on the run's
//!   thread), and `--stop-poll-delay-ns=N` sleeps N ns in every SAT stop poll
//!   (`test_seams::delay_each_stop_poll`: ay-chc's own solves' and the
//!   executor's), slice 8's slow host, which also slows the inside of a solve.
//!   For K times slower: `ps = (K - 1) * wall_ns * 1000 * a / ticks` and
//!   `ns = (K - 1) * wall_ns * (1 - a) / polls` for a share `a` of the delay
//!   put on the ticks.
//!
//! A file whose result is the same on both runs but whose `work` differs had
//! its search steered by a clock.

use std::error::Error;
use std::io::Write;
use std::time::{Duration, Instant};

use ay_core::resource::test_seams;
use sha2::{Digest, Sha256};

#[derive(Clone)]
struct Args {
    path: String,
    timeout: Duration,
    effort: Option<u64>,
    token: bool,
    threads: usize,
    charge_delay: Duration,
    tick_delay_ps: u64,
    stop_poll_delay: Duration,
}

const USAGE: &str = "usage: chc_proof_work FILE [--timeout-ms=N] [--effort=B] [--token] \
                     [--threads=K] [--charge-delay-ns=N] [--tick-delay-ps=N] \
                     [--stop-poll-delay-ns=N]";

fn parse_args() -> Result<Args, Box<dyn Error>> {
    let mut args = std::env::args().skip(1);
    let path = args.next().ok_or(USAGE)?;
    let mut parsed = Args {
        path,
        timeout: Duration::from_millis(5000),
        effort: None,
        token: false,
        threads: 1,
        charge_delay: Duration::ZERO,
        tick_delay_ps: 0,
        stop_poll_delay: Duration::ZERO,
    };
    for arg in args {
        if let Some(ms) = arg.strip_prefix("--timeout-ms=") {
            parsed.timeout = Duration::from_millis(ms.parse()?);
        } else if let Some(ticks) = arg.strip_prefix("--effort=") {
            parsed.effort = Some(ticks.parse()?);
        } else if arg == "--token" {
            parsed.token = true;
        } else if let Some(k) = arg.strip_prefix("--threads=") {
            parsed.threads = k.parse::<usize>()?.max(1);
        } else if let Some(ns) = arg.strip_prefix("--charge-delay-ns=") {
            parsed.charge_delay = Duration::from_nanos(ns.parse()?);
        } else if let Some(ps) = arg.strip_prefix("--tick-delay-ps=") {
            parsed.tick_delay_ps = ps.parse()?;
        } else if let Some(ns) = arg.strip_prefix("--stop-poll-delay-ns=") {
            parsed.stop_poll_delay = Duration::from_nanos(ns.parse()?);
        } else {
            return Err(format!("unknown argument {arg}; {USAGE}").into());
        }
    }
    Ok(parsed)
}

fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

/// One run on this thread (the tick delay is this thread's).
fn run(args: &Args) -> Result<serde_json::Value, Box<dyn Error>> {
    let problem = ay_chc::ChcParser::parse(&std::fs::read_to_string(&args.path)?)?;
    let mut config = ay_chc::PdrConfig::production(false).with_effort(args.effort);
    config.solve_timeout = Some(args.timeout);
    if args.token {
        config.cancellation_token = Some(ay_chc::CancellationToken::new());
    }
    test_seams::delay_each_tick_picos(args.tick_delay_ps);
    let started = Instant::now();
    let run = ay_chc::engines::solve_pdr_proof(problem, config)?;
    let wall = started.elapsed();
    test_seams::delay_each_tick_picos(0);
    let metadata = run.metadata().to_json_value();
    Ok(serde_json::json!({
        "file": args.path,
        "result": metadata["result"],
        "accepted": run.accepted_as_proof(),
        "metadata_sha256": sha256_hex(metadata.to_string().as_bytes()),
        "model_sha256": run.model_artifact().sha256(),
        "wall_ms": wall.as_secs_f64() * 1000.0,
        "work": run.work().map(ay_chc::ChcRunWork::to_json_value),
    }))
}

fn line(args: &Args, result: Result<serde_json::Value, Box<dyn Error>>) -> serde_json::Value {
    result.unwrap_or_else(
        |error| serde_json::json!({ "file": args.path, "error": error.to_string() }),
    )
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = parse_args()?;
    test_seams::delay_each_charge(args.charge_delay);
    test_seams::delay_each_stop_poll(args.stop_poll_delay);
    let charges_before = test_seams::charges();
    let polls_before = test_seams::stop_polls();
    let mut out = if args.threads == 1 {
        line(&args, run(&args))
    } else {
        let lines: Vec<serde_json::Value> = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..args.threads)
                .map(|_| scope.spawn(|| line(&args, run(&args))))
                .collect();
            handles
                .into_iter()
                .map(|handle| {
                    handle
                        .join()
                        .unwrap_or_else(|_| serde_json::json!({ "error": "thread panicked" }))
                })
                .collect()
        });
        serde_json::Value::Array(lines)
    };
    let charges = test_seams::charges() - charges_before;
    let polls = test_seams::stop_polls() - polls_before;
    test_seams::delay_each_charge(Duration::ZERO);
    test_seams::delay_each_stop_poll(Duration::ZERO);
    let seams = serde_json::json!({
        "charge_delay_ns": u64::try_from(args.charge_delay.as_nanos()).unwrap_or(u64::MAX),
        "tick_delay_ps": args.tick_delay_ps,
        "stop_poll_delay_ns": u64::try_from(args.stop_poll_delay.as_nanos()).unwrap_or(u64::MAX),
        "charges": charges,
        "stop_polls": polls,
        "effort": args.effort,
        "timeout_ms": u64::try_from(args.timeout.as_millis()).unwrap_or(u64::MAX),
        "token": args.token,
        "threads": args.threads,
    });
    if let serde_json::Value::Object(map) = &mut out {
        map.insert("seams".to_owned(), seams);
    } else {
        out = serde_json::json!({ "runs": out, "seams": seams });
    }
    writeln!(std::io::stdout().lock(), "{out}")?;
    Ok(())
}
