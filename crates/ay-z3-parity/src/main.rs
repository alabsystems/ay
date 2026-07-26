// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay-z3-parity` — a mechanistic compatibility auditor.
//!
//! It measures named compatibility surfaces between the AY SMT solver
//! (`libay_ffi`) and Z3 (`libz3`):
//!
//! * `symbols` audits exported-symbol coverage — whether each `Z3_*` symbol
//!   found live via `nm -gU` is `dlsym`-able in the AY library.
//! * `diff` audits verdict agreement on a supplied SMT-LIB2 corpus by running
//!   it through both libraries via `Z3_eval_smtlib2_string`.
//!
//! Both libraries are `dlopen`ed at runtime; nothing is linked at build time,
//! so the tool works against ANY two Z3-ABI shared objects.

mod behavior;
mod bench;
mod diff;
mod fetch;
mod inprocess;
mod loader;
mod scoreboard;
mod smtlib_conformance;
mod symbols;

use std::path::PathBuf;
use std::process::ExitCode;

const DEFAULT_AY: &str = "target/debug/libay_ffi.dylib";
const DEFAULT_Z3: &str = "/opt/homebrew/lib/libz3.dylib";
const DEFAULT_DIFF_TIMEOUT_SECS: u64 = 10;
const DEFAULT_BENCH_TIMEOUT_SECS: u64 = 20;
const DEFAULT_BENCH_JSON: &str = "ay-z3-bench.json";
const DEFAULT_BENCH_REPORT: &str = "ay-z3-bench.md";
const DEFAULT_SCOREBOARD_JSON: &str = "ay-z3-scoreboard.json";

fn usage() -> &'static str {
    "\
ay-z3-parity — audit named AY/Z3 compatibility surfaces

USAGE:
  ay-z3-parity symbols [--ay <path>] [--z3 <path>] [--json]
      Audit SYMBOL coverage: nm -gU the libz3 reference set, dlsym each in AY.
      Exit 0 iff no libz3 symbol is missing from AY.

  ay-z3-parity fetch <dest-dir> [--sample N | --all] [--max-mb M]
                     [--divisions d1,d2,...] [--record ID] [--list]
      Materialize the SMT-LIB corpus from Zenodo (record 11061097 by default)
      into <dest-dir>/<DIVISION>/. Queries the API for every <DIV>.tar.zst
      archive, downloads each, verifies its published md5 (a mismatch skips just
      that division), extracts the zstd tarball, and writes its .smt2 files flat
      ('/'->'__').
      COMPLETE BY DEFAULT: every division, every file, NO size cap (84 divisions
      / ~4.8 GB for SMT-LIB 2024 non-incremental). Narrowing is opt-in and always
      reported: --sample N takes an evenly-spaced subset (indices
      floor(i*total/N)), --divisions is an allowlist, --max-mb M skips archives
      over M MB. Any of those prints an `!! INCOMPLETE COVERAGE` block naming
      every exclusion, so a partial corpus can never read as a complete one.
      --list is a dry run: shows what the current options would include or
      exclude and downloads nothing. See `fetch --help` for details.

  ay-z3-parity diff <corpus-dir-or-file>... [--ay <path>] [--z3 <path>]
                     [--timeout <secs>] [--json] [--oracle declared]
      Audit verdict agreement: run every .smt2 script through BOTH libs and
      compare verdicts. Unknowns and timeouts are reported; exit non-zero iff
      any sat-vs-unsat DISAGREE.

      With --oracle declared: HERMETIC mode — needs NO z3. Run every .smt2
      through the AY lib ONLY and compare AY's verdict against the file's own
      (set-info :status sat|unsat) ground truth. A sat where the file declares
      unsat (or vice-versa) is a SOUNDNESS FAIL; unknown/timeout is tolerated;
      files without a decided :status are skipped. Exit non-zero iff any WRONG.

  ay-z3-parity classify <corpus-dir-or-file>... [--timeout <secs>] [--json]
      IN-PROCESS differential oracle (extracted from deductive-checks at R1 of the
      two-language design): replay every .smt2 through ay AS A LIBRARY
      (ay_frontend::parse + ay_dpll::Executor, catch_unwind, wall deadline)
      and classify against the file's own (set-info :status sat|unsat)
      ground truth. HERMETIC — needs no z3 and no dylib build. Buckets:
      agree / ay_incomplete (UnknownReason-coded histogram) / timeout /
      parse_error / UNSOUND-DISAGREE. Exit non-zero iff any UNSOUND-DISAGREE.

  ay-z3-parity bench <corpus-root>... [--ay <path>] [--z3 <path>]
                     [--timeout <secs>] [--jobs <n>] [--json]
                     [--json-out <path>] [--report <path>]
      Benchmark CAMPAIGN: run every .smt2 under each corpus root through BOTH
      libs, per division (= <root-name>/<top-level-subdir>). Each (file,
      solver) pair runs in an isolated child process with eval-only wall
      timing and a hard-kill timebox. Emits a per-division table, a JSON
      certificate (--json-out) and a markdown report (--report) with an
      auto-populated \"where z3 wins\" section. Exit non-zero iff any
      sat-vs-unsat DISAGREE. Requested jobs are capped by `_oom_guard.py`;
      the exact enforced memory/core/timeout envelope is persisted.

  ay-z3-parity scoreboard <corpus-root> --ay <path> [--ay-cli <path>]
                     [--z3 <path>] [--jobs <n>] [--timeout <secs>]
                     [--json-out <path>] [--baseline <path>]
                     [--divisions <d1,d2,...>] [--checkpoint <path>] [--resume]
                     [--sample-per-division <n>] [--seed <u64>] [--progress <path>]
      PROGRESS SCOREBOARD across every division subdir under <corpus-root>, on
      TWO metrics at once: the z3-AGREEMENT metric and AY's OWN fail-closed
      SELF-CERTIFICATION metric. Each .smt2 is run through AY (the FFI dylib),
      z3 (libz3), and `ay solve --self-check` (the CLI binary), each in a fresh
      timeboxed child (reusing the `bench` isolation/timing plumbing). Per
      division it reports:
        SOLVED%   = ay-agree / z3-decided
        SELFCERT% = files AY self-certifies / files AY decides  (the honest,
                    z3-independent metric)
        BEYOND    = files AY decides where z3 does not
        GEO ay/z3 = geomean WALL ratio over decided-by-both (<1 = AY faster)
        MEM ay/z3 = geomean PEAK-RSS ratio over decided-by-both above 5MB
                    (<1 = AY leaner); each successful bench child self-reports
                    getrusage(RUSAGE_SELF) (Darwin bytes, Linux KiB normalized)
        RATING    = highest tier reached (floors: WALL 10ms, RSS 5MB):
                    PAR      = DISAGREE 0, AY decides every z3 decision, and
                               ay_wall <= z3_wall on every decided-by-both file
                    SUPERIOR = PAR + ay_wall <= 0.5*z3_wall (>=2x) on every such
                               file + complete RSS evidence + ay_rss < 0.8*z3_rss
                               on every one over 5MB; missing RSS blocks this tier
                    PERFECT  = SUPERIOR + AY decides 100% of the track's files
                    below(uN,sM,dK,mJ) / PAR(xN,mM,rK) / SUPERIOR(uN) show blockers
        DISAGREE  = sat-vs-unsat conflicts (AY vs z3) — MUST be 0
      Emits a compact per-division table (+ TOTAL) and a JSON certificate
      (--json-out) with all raw per-division/per-file data. With --baseline
      <prior scoreboard json>, adds a DELTA column (solved/selfcert/rating vs
      the baseline) so progress is trackable across runs. Works with z3 absent
      (z3 columns become n/a; AY still reports decided + self-cert). The `ay`
      CLI is found via --ay-cli, else a sibling `ay` next to the FFI dylib,
      else target/release/ay. Self-certification is enabled only when the CLI
      and FFI build identities prove the same source revision. Exit non-zero
      (with a prominent WARNING) iff any DISAGREE or any self-check-vs-eval
      contradiction.
      Requested jobs are capped by `_oom_guard.py`; the exact enforced
      memory/core/timeout envelope is persisted in the certificate.

  ay-z3-parity behavior [--ay <path>] [--z3 <path>] [--json]
      Audit behavior on the honest-divergence surface: drive the same
      minimal inputs through BOTH libs (char↔BV, transitive closure,
      on_clause, Spacer extras, relation getters, polymorphic instantiation,
      HO-seq solving) and compare outcome CLASSES (ok-value / error / inert /
      verdict). Prints the honest residue where libz3 is more capable.
      Exit non-zero iff any pair of produced values/verdicts CONFLICTS.

  ay-z3-parity smtlib-conformance <profile|init|run|check|receipt-check> ...
      Maintain the fail-closed SMT-LIB 2.7 + exact Z3 5.0.0 conformance
      contract. The contract has closed dimensions for grammar, commands,
      theories, logics, typing/scope, command state, SAT models, UNSAT proofs,
      unknown policy, the Z3 overlay, corpus closure, and gate integrity.
      `check` is completion-gated by default and exits 0 only when every source
      inventory is closed and every requirement has exhaustive, hash-bound
      passing evidence. `--audit-only` is the explicit weaker status mode.
      See `smtlib-conformance --help` for the evidence protocol.

DEFAULTS:
  --ay        target/debug/libay_ffi.dylib
  --ay-cli    sibling `ay` next to --ay, else target/release/ay (scoreboard)
  --z3        /opt/homebrew/lib/libz3.dylib
  --timeout   10 (diff) / 20 (bench, scoreboard)  per-(file,solver) wall seconds
  --jobs      1    (bench/scoreboard; requested workers, host planner may cap)
  --json-out  ay-z3-bench.json (bench) / ay-z3-scoreboard.json (scoreboard)
  --report    ay-z3-bench.md   (bench only)
  --baseline  (none; scoreboard DELTA column vs a prior scoreboard json)
  --divisions (all; scoreboard/fetch: comma-separated divisions to include)
  --sample-per-division (all; scoreboard: run at most N files from EACH
              division, chosen by hashing (seed, path). A full SMT-LIB pass is
              438k files / ~300h; a per-track sample is what makes this runnable
              on a schedule. Small divisions are taken whole, so every track
              stays represented, and the certificate records selected/available
              per track so a sampled number can never read as a full one)
  --seed      0 (scoreboard: sampling seed. Selection is a pure function of
              (seed, path) — same seed and corpus give the same set on any
              machine, so two runs are comparable; a new seed is an independent
              sample. Ranking is hash-based, not index-based, so growing the
              corpus does not reshuffle the existing selection)
  --progress  (none; scoreboard: path to a JSON status file rewritten every ~5s
              with done/total, files/min, ETA, pid and the run's parameters.
              Written atomically, so a reader never sees a partial document)
  --checkpoint <json-out>.checkpoint.jsonl (scoreboard; ALWAYS written, one
              line per completed file, flushed immediately. The certificate is
              only written at the end, so this is what a multi-day corpus run
              survives a crash with)
  --resume    (off; scoreboard: reuse completed files from the checkpoint
              instead of re-running them. Opt-in, and refused outright if the
              journal's header does not match this run's corpus, timeout and
              binary hashes — resuming across a rebuild would produce a
              certificate describing neither run)
  --sample    (unset)  (fetch; EVERY file per division by default. --sample N
                        narrows to N evenly-spaced files and is reported as
                        incomplete coverage)
  --max-mb    (unset)  (fetch; NO size cap by default, so every division is
                        fetched. --max-mb M skips larger archives and is
                        reported as incomplete coverage)
  --record    11061097 (fetch; Zenodo record id)
"
}

struct Parsed {
    ay: PathBuf,
    ay_cli: Option<PathBuf>,
    z3: PathBuf,
    json: bool,
    timeout: Option<u64>,
    jobs: usize,
    json_out: PathBuf,
    json_out_set: bool,
    report: PathBuf,
    oracle: Option<String>,
    baseline: Option<PathBuf>,
    divisions: Option<Vec<String>>,
    checkpoint: Option<PathBuf>,
    resume: bool,
    sample: Option<usize>,
    seed: u64,
    progress: Option<PathBuf>,
    positionals: Vec<PathBuf>,
}

fn parse(rest: &[String]) -> Result<Parsed, String> {
    let mut ay = PathBuf::from(DEFAULT_AY);
    let mut ay_cli = None;
    let mut z3 = PathBuf::from(DEFAULT_Z3);
    let mut json = false;
    let mut timeout = None;
    let mut jobs = 1usize;
    let mut json_out = PathBuf::from(DEFAULT_BENCH_JSON);
    let mut json_out_set = false;
    let mut report = PathBuf::from(DEFAULT_BENCH_REPORT);
    let mut oracle = None;
    let mut baseline = None;
    let mut divisions = None;
    let mut checkpoint = None;
    let mut resume = false;
    let mut sample = None;
    let mut seed = 0u64;
    let mut progress = None;
    let mut positionals = Vec::new();

    let mut it = rest.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--ay" => ay = PathBuf::from(it.next().ok_or("--ay needs a path")?),
            "--ay-cli" => ay_cli = Some(PathBuf::from(it.next().ok_or("--ay-cli needs a path")?)),
            "--z3" => z3 = PathBuf::from(it.next().ok_or("--z3 needs a path")?),
            "--json" => json = true,
            "--json-out" => {
                json_out = PathBuf::from(it.next().ok_or("--json-out needs a path")?);
                json_out_set = true;
            }
            "--report" => report = PathBuf::from(it.next().ok_or("--report needs a path")?),
            "--baseline" => {
                baseline = Some(PathBuf::from(it.next().ok_or("--baseline needs a path")?));
            }
            "--checkpoint" => {
                checkpoint = Some(PathBuf::from(it.next().ok_or("--checkpoint needs a path")?));
            }
            "--resume" => resume = true,
            "--sample-per-division" => {
                sample = Some(
                    it.next()
                        .ok_or("--sample-per-division needs a count")?
                        .parse()
                        .map_err(|_| "--sample-per-division must be a positive integer")?,
                );
            }
            "--seed" => {
                seed = it
                    .next()
                    .ok_or("--seed needs an integer")?
                    .parse()
                    .map_err(|_| "--seed must be a u64")?;
            }
            "--progress" => {
                progress = Some(PathBuf::from(it.next().ok_or("--progress needs a path")?));
            }
            "--divisions" => {
                let list = it
                    .next()
                    .ok_or("--divisions needs a comma-separated list")?;
                divisions = Some(
                    list.split(',')
                        .map(str::trim)
                        .filter(|s| !s.is_empty())
                        .map(str::to_string)
                        .collect(),
                );
            }
            "--oracle" => {
                let val = it.next().ok_or("--oracle needs a value (declared)")?;
                if val != "declared" {
                    return Err(format!("unknown --oracle value: {val} (only `declared`)"));
                }
                oracle = Some(val.clone());
            }
            "--timeout" => {
                timeout = Some(
                    it.next()
                        .ok_or("--timeout needs a number")?
                        .parse()
                        .map_err(|_| "--timeout must be an integer number of seconds")?,
                );
            }
            "--jobs" => {
                jobs = it
                    .next()
                    .ok_or("--jobs needs a number")?
                    .parse()
                    .map_err(|_| "--jobs must be a positive integer")?;
                if jobs == 0 {
                    return Err("--jobs must be at least 1".to_string());
                }
            }
            other if other.starts_with("--") => return Err(format!("unknown flag: {other}")),
            other => positionals.push(PathBuf::from(other)),
        }
    }
    Ok(Parsed {
        ay,
        ay_cli,
        checkpoint,
        resume,
        sample,
        seed,
        progress,
        z3,
        json,
        timeout,
        jobs,
        json_out,
        json_out_set,
        report,
        oracle,
        baseline,
        divisions,
        positionals,
    })
}

fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().collect();
    let (cmd, rest) = match argv.split_first().and_then(|(_, tail)| tail.split_first()) {
        Some((c, r)) => (c.as_str(), r),
        None => {
            print!("{}", usage());
            return ExitCode::from(2);
        }
    };

    if matches!(cmd, "-h" | "--help" | "help") {
        print!("{}", usage());
        return ExitCode::SUCCESS;
    }

    // `fetch` has a divergent flag set (--sample/--all/--max-mb/--record/--list)
    // and needs no dylibs, so it parses its own args ahead of the shared parser.
    if cmd == "fetch" {
        return ExitCode::from(fetch::run(rest) as u8);
    }
    if matches!(cmd, "smtlib-conformance" | "smtlib") {
        return ExitCode::from(smtlib_conformance::run(rest) as u8);
    }

    let parsed = match parse(rest) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("error: {e}\n\n{}", usage());
            return ExitCode::from(2);
        }
    };

    let code = match cmd {
        "symbols" => symbols::run(&parsed.ay, &parsed.z3, parsed.json),
        "behavior" => behavior::run(&parsed.ay, &parsed.z3, parsed.json),
        "diff" => {
            if parsed.positionals.is_empty() {
                eprintln!(
                    "error: `diff` needs at least one corpus dir or .smt2 file\n\n{}",
                    usage()
                );
                2
            } else if parsed.oracle.as_deref() == Some("declared") {
                // Hermetic mode: AY vs each file's own (set-info :status ...).
                diff::run_declared(
                    &parsed.ay,
                    &parsed.positionals,
                    parsed.timeout.unwrap_or(DEFAULT_DIFF_TIMEOUT_SECS),
                    parsed.json,
                )
            } else {
                diff::run(
                    &parsed.ay,
                    &parsed.z3,
                    &parsed.positionals,
                    parsed.timeout.unwrap_or(DEFAULT_DIFF_TIMEOUT_SECS),
                    parsed.json,
                )
            }
        }
        "classify" => {
            if parsed.positionals.is_empty() {
                eprintln!(
                    "error: `classify` needs at least one corpus dir or .smt2 file\n\n{}",
                    usage()
                );
                2
            } else {
                inprocess::run_classify(
                    &parsed.positionals,
                    parsed.timeout.unwrap_or(DEFAULT_DIFF_TIMEOUT_SECS),
                    parsed.json,
                )
            }
        }
        "bench" => {
            if parsed.positionals.is_empty() {
                eprintln!(
                    "error: `bench` needs at least one corpus root\n\n{}",
                    usage()
                );
                2
            } else {
                bench::run(&bench::BenchConfig {
                    ay: parsed.ay,
                    z3: parsed.z3,
                    roots: parsed.positionals,
                    timeout_secs: parsed.timeout.unwrap_or(DEFAULT_BENCH_TIMEOUT_SECS),
                    jobs: parsed.jobs,
                    json_stdout: parsed.json,
                    json_out: parsed.json_out,
                    report_out: parsed.report,
                })
            }
        }
        "scoreboard" => {
            if parsed.positionals.is_empty() {
                eprintln!("error: `scoreboard` needs a corpus root\n\n{}", usage());
                2
            } else if parsed.positionals.len() > 1 {
                eprintln!(
                    "error: `scoreboard` takes exactly one corpus root (got {})\n\n{}",
                    parsed.positionals.len(),
                    usage()
                );
                2
            } else {
                let json_out = if parsed.json_out_set {
                    parsed.json_out
                } else {
                    PathBuf::from(DEFAULT_SCOREBOARD_JSON)
                };
                scoreboard::run(&scoreboard::ScoreboardConfig {
                    ay: parsed.ay,
                    ay_cli: parsed.ay_cli,
                    z3: parsed.z3,
                    root: parsed
                        .positionals
                        .into_iter()
                        .next()
                        .expect("one positional"),
                    timeout_secs: parsed.timeout.unwrap_or(DEFAULT_BENCH_TIMEOUT_SECS),
                    jobs: parsed.jobs,
                    json_out,
                    baseline: parsed.baseline,
                    divisions: parsed.divisions,
                    checkpoint: parsed.checkpoint,
                    resume: parsed.resume,
                    sample: parsed.sample,
                    seed: parsed.seed,
                    progress: parsed.progress,
                })
            }
        }
        // Hidden child mode used by `bench`: evaluate ONE file in ONE library
        // and print strict wall/RSS headers followed by the raw solver output.
        "bench-one" => {
            if parsed.positionals.len() != 2 {
                eprintln!("error: `bench-one` needs exactly <lib> <file>");
                2
            } else {
                bench::run_child(&parsed.positionals[0], &parsed.positionals[1])
            }
        }
        other => {
            eprintln!("error: unknown subcommand `{other}`\n\n{}", usage());
            2
        }
    };

    ExitCode::from(code as u8)
}
