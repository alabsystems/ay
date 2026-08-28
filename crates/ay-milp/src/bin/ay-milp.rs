// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! `ay-milp` — the solver's command line, with certificates as a first-class
//! exit.
//!
//! This replaces a pile of environment-variable-gated modes in
//! `examples/mps_solve.rs` with real subcommands and real flags. Two things
//! motivated it beyond tidiness:
//!
//! 1. **The witness could not get out of an `Optimal`.** `AY_DUMP_SOL` lived on
//!    the `Feasible` match arm only, so `AY_DUMP_SOL=/tmp/x mps_solve
//!    markshare1.mps 30` printed `OPTIMAL 1` and created NO FILE. The one thing
//!    you could not extract was the witness of a PROVEN optimum. That is
//!    backwards, and `--emit-witness` fixes it on every verdict.
//! 2. **A typo in an `AY_*` name is silent.** `AY_MILP_NO_CUTZ=1` is a no-op, so
//!    a measurement campaign that sets it records a result for the wrong arm.
//!    Every run of this binary audits the environment against the ledger in
//!    `knobs.rs` and warns loudly.
//!
//! Every environment variable the old modes used still works. Deleting the
//! names in the same change that adds flags would break the journal's
//! measurement scripts, and a paper trail that stops reproducing is a real
//! loss — so they are ALIASES, with a one-line deprecation warning, and the
//! flag wins when both are given.

use std::io::Write as _;
use std::process::ExitCode;
use std::time::{Duration, Instant};

use ay_milp::cert_io;
use ay_milp::{BabSession, ColKind, MpsProblem, Outcome, SolveOpts, UnknownReason};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use ay_milp::engine_cli as engine_flags;
use ay_milp::engine_cli::Flags;

#[path = "ay_milp/solve_options.rs"]
mod solve_options;

const USAGE: &str = "\
ay-milp — MILP/LP engine with certified verdicts

USAGE
  ay-milp solve <file.mps[.gz]> [options]
  ay-milp verify --model <file.mps> --cert <file.ayc> [--accept-replay] [--exit-zero]
  ay-milp check-point --model <file.mps> --point <file.sol> [--repair-continuous]
  ay-milp diag <root-closure|lp-only|shipped-lp|dualfix|block-angular|margin-row|cross-check|profile> <file.mps> [--time-limit <sec>] [--memory-budget <bytes>]
      lp-only    ITERATION ECONOMICS ONLY: one cold float walk, no ladder, nothing certified.
                 Its status and objective are NOT solver behaviour; every line it prints says so.
      shipped-lp the SAME LP through the lane a solve actually runs, with its certified verdict.
  ay-milp knobs [--list] [--bucket <b>] [--audit] [--deprecated]
  ay-milp features --list
  ay-milp replay-claims

solve options
  --time-limit <secs>          wall-clock limit (default 60)
  --threads <n>                worker threads (>1 opts out of determinism)
  --seed <n>                   RNG seed
  --deterministic|--no-deterministic
  --memory-budget <bytes>      open-node/SAT-ReLU logical memory budget
  --tree-cert-leaves <n>       tree-certificate leaf budget (default 256; 0 = off)
  --seed-solution <path>       reference incumbent, `name value` per line (advice only)
  --require <none|witness|full>   evidence posture (DEFAULT: witness)
  --emit-cert <path.ayc>       certificate path (DEFAULT: <input>.ayc)
  --no-emit-cert               opt out of certificate emission
  --emit-cert-max-bytes <n>    cap; an overflowing block is DROPPED and its claim downgraded
  --opt-tree-work <n>          DETERMINISTIC work budget for the whole-tree OPTIMALITY proof,
                               in exact-arithmetic passes (0 = off). Default 24000000/nnz,
                               because one pass costs O(nnz). The evidence a run emits is a
                               function of this, never of machine load.
  --opt-tree-grid <bits>       snap optimality-tree duals to 2^-bits before exactifying
                               (default 12; 0 = off).
                               Halves certificate bytes at no leaf cost; weak duality holds for
                               ANY feasible y, so a snapped y is a valid bound, never a wrong one.
  --opt-tree-leaves <n>        leaf budget for the same (default 20000; 0 = off)
  --opt-tree-secs <secs>       wall-clock SAFETY NET for the same (default 600; 0 = no net).
                               Not the budget: if this ever binds the run says `deadline` and
                               its evidence was load-dependent.
  --no-opt-tree                opt out of whole-tree optimality derivation
  --emit-witness <path>        write the witness on ANY verdict that has one
  --witness-format <ay|sol|rational>   default: rational
  --format <line|json>         stdout shape (default line)

verify exits:  0 VERIFIED   10 UNVERIFIED   11 PARTIAL   20 REFUTED   30 MISMATCH
The word VERIFIED is reserved: a REPLAY claim never earns exit 0.
PARTIAL (11) refines UNVERIFIED, never VERIFIED: some claim re-verified exactly
and nothing was refuted, but a claim carries no checkable evidence. It is a
non-zero exit. `verify` also prints a CLAIMS census line naming every claim by
standing (verified / refuted / unbacked), so a consumer never has to infer which
half of an `optimal` was proved from the aggregate word alone.
";

/// THE OPTIMALITY-TREE BUDGET, and it is deterministic. In `work` units TIMES
/// the model's matrix nonzeros — see [`default_opt_tree_work`], which divides.
///
/// # Why the budget is nnz-weighted, measured
///
/// One `work` unit is one exact-arithmetic pass over the model
/// (`ay_milp::OptTreeReport::work`), and a pass costs O(nnz). A FLAT unit cap
/// therefore means wildly different wall times: at a flat 8,000 units, `air03`
/// (91,028 nnz) took **508.6 s** while `dcmulti` (1,315 nnz) took **0.385 s**.
///
/// Measured on the 30-instance `~/ay-bench/milp-gate` corpus plus `f2gap40400`
/// and `supportcase16`, 27 usable derivations, comparing candidate currencies
/// by the wall each would cost at a cap set to preserve every certificate:
///
/// ```text
///   currency            median predicted   worst predicted
///   leaves (the shipped knob)     58.7 s          950.7 s
///   work (flat)                   23.8 s       89,825.3 s
///   work x sqrt(nnz)              21.1 s        2,188.7 s
///   work x (rows+cols)            13.9 s          368.0 s
///   nodes x nnz                   15.7 s          231.5 s
///   work x nnz            -->     10.1 s          102.5 s
/// ```
///
/// `work x nnz` wins on both, and by two to three orders of magnitude on the
/// worst case. It is also the currency with the tightest measured rate spread
/// (max/min 257x across the corpus, against 50,449x for flat `work`).
///
/// # Why THIS number
///
/// EVIDENCE PRESERVATION sets it. `work` for an instance that CERTIFIES is the
/// total the derivation needed, not a truncation, and it is deterministic — so
/// the floor is exact rather than statistical. The eight instances that certify
/// at the old 5 s default spend, in `work x nnz`:
///
/// ```text
///   misc03 20,811,261   stein27 19,353,600   supportcase16 1,468,740
///   f2gap40400 1,135,200   flugpl 252,678   p0033 198,254
///   gt2 84,224   enigma 289
/// ```
///
/// 24,000,000 clears the binding one (`misc03`) by 15%, which on a
/// deterministic quantity is margin rather than hope, and every other
/// certificate by 16x or more.
const OPT_TREE_WORK_NNZ: u64 = 24_000_000;

/// The default work budget for `model`, in `OptTreeReport::work` units.
///
/// Size-derived, exactly as the exact rim's own `Budget::default_iters(vars)`
/// is. `max(1)` rather than a floor: on a model whose nonzeros already exceed
/// the whole budget the honest answer is one node and an immediate decline, not
/// a token allowance that costs minutes to spend.
fn default_opt_tree_work(model: &ay_milp::Model) -> u64 {
    let nnz: u64 = (0..model.num_rows())
        .filter_map(|r| model.row_at(r))
        .map(|r| model.row(r).0.len() as u64)
        .sum();
    (OPT_TREE_WORK_NNZ / nnz.max(1)).max(1)
}

/// The leaf budget. It is REACHED now, and it was not before.
///
/// Under the shipped 5 s clock it could not fire at all: across 164 derivations
/// over 41 OPTIMAL instances, 136 declined on the DEADLINE and ZERO on this.
/// With the primary bound denominated in work it does — measured on this build,
/// `lseu` commits **20,270** leaves and `markshare1` **20,165** against a cap of
/// 20,000. `leaves <= nodes <= work` is structural (one leaf per node, one unit
/// per node), so the cap is reachable exactly when a model is sparse enough for
/// its work budget to exceed it: `lseu` (309 nnz) draws 77,669 units.
///
/// It is NOT the terminal decline on either of those runs, and that is a
/// property of the terminal reason rather than of this cap: the leaf cap trips
/// deep in a subtree, the descent unwinds, and the parent then spends the rest
/// of the budget in the exact rim, so LAST-WRITER-WINS reports `work-cap`.
/// `OptTreeReport::leaf_capped` counts the event separately for exactly that
/// reason — the same repair `depth_capped` already had — and the CLI prints it.
///
/// It stays a separate number rather than being folded into the work cap
/// because it bounds the ARTIFACT, not the search: a `boundleaf` carries one
/// multiplier per column with a nonzero reduced cost, so leaves x columns is
/// what turns `misc07` into 191 MB.
const OPT_TREE_LEAVES: usize = 20_000;

/// The wall-clock SAFETY NET, in seconds. NOT the budget.
///
/// It exists only so that a model whose per-unit cost is far outside anything
/// measured cannot make a `solve` appear to hang.
///
/// SAY WHAT WAS MEASURED, NOT WHAT IS PREDICTED. An earlier draft called this
/// "sized NOT TO BIND", which is a claim about every future model and cannot be
/// supported. What was actually observed: it did NOT bind on 17 declines
/// spanning 1-minute load 3..102, and the margin on the worst instance
/// (`mod008`, 243 s at load ~100) is only ~2.5x — not the ~6x a quiet-box
/// calibration suggests, because the rim's per-iteration cost is itself
/// load-sensitive. On a quiet box the worst derivation measured is `nw04` at
/// 100.8 s and the median is 10.1 s.
///
/// Note also that the net can be overshot: the descent and the rim are two
/// phases, each checking the deadline, so in principle a run can spend up to
/// ~2x this before stopping.
///
/// If it ever fires the run reports `deadline` rather than `work-cap` — the two
/// are deliberately different tags — which is the signal that this run's
/// evidence was load-dependent after all.
const OPT_TREE_BACKSTOP_SECS: f64 = 600.0;

/// Wall clock at the first instruction of `main` in the FINAL (post-`arm`)
/// process image, for `--phase-ledger`.
///
/// Everything before this — the caller's `fork`/`exec`, dyld, the Rust runtime
/// prologue, and `arm`'s re-exec chain through `taskpolicy` — is invisible from
/// in-process and has to be differenced against the caller's own wall clock.
/// That difference is exactly the term a harness timing `subprocess.run`
/// charges to the solver and an in-process API timing (`gp.Env` + `gp.read` +
/// `optimize`) does not pay at all.
static MAIN_T0: std::sync::OnceLock<Instant> = std::sync::OnceLock::new();

fn main() -> ExitCode {
    // FIRST statement of main: arm() re-execs this process under a kernel-held
    // memory bound, so anything above it is discarded work, and it sets an env
    // var (sound only while single-threaded). See crates/ay-sys/src/govern.rs.
    ay_sys::govern::arm();
    // Immediately AFTER arm(), not before. A `MAIN_T0.set` above it violated the
    // invariant the comment right there states, and bought nothing: arm() re-execs,
    // so the pre-exec process that ran that line is replaced and its `Instant` is
    // discarded — the value actually read at the ledger below is the one set by the
    // post-exec process on its own pass through main. In that process arm() returns
    // on an env-var check, so anchoring here rather than one line earlier moves
    // `in_main` by an env lookup. The exec chain is recovered against the wall
    // clock further down, exactly as the ledger comment describes.
    let _ = MAIN_T0.set(Instant::now());

    let args: Vec<String> = std::env::args().skip(1).collect();
    // Help is accepted ANYWHERE, not just first: the subcommand parsers refuse
    // an unknown flag now, and `ay-milp solve --help` asking for help must not
    // be answered with "unknown flag `--help`".
    let no_args = args.is_empty();
    if no_args || args.iter().any(|a| a == "-h" || a == "--help") {
        print!("{USAGE}");
        return if no_args {
            ExitCode::from(2)
        } else {
            ExitCode::SUCCESS
        };
    }
    // THE CORRECTNESS FIX, on every invocation: an `AY_*` name nothing reads is
    // a campaign silently measuring the wrong arm. It now REFUSES rather than
    // warns — a warning in a harness log that nobody reads is not a guard.
    // `knobs --audit` is exempt: reporting the problem is what it is for.
    let auditing = args[0] == "knobs";
    if !audit_environment() && !auditing {
        return ExitCode::from(2);
    }

    let rest = &args[1..];
    match args[0].as_str() {
        "solve" => cmd_solve(rest),
        "verify" => cmd_verify(rest),
        "check-point" => cmd_check_point(rest),
        "diag" => cmd_diag(rest),
        "knobs" => cmd_knobs(rest),
        "features" => cmd_features(rest),
        "replay-claims" => cmd_replay_claims(),
        other => {
            eprintln!("ay-milp: unknown subcommand `{other}`\n");
            print!("{USAGE}");
            ExitCode::from(2)
        }
    }
}

// ---------------------------------------------------------------------------
// Environment audit and the deprecation bridge
// ---------------------------------------------------------------------------

/// Report the environment audit. Returns `false` if the run must not proceed.
///
/// This used to warn and continue. It fails, because a warning is not a guard:
/// see [`ay_milp::EnvAudit::is_fatal`]. `AY_ALLOW_UNKNOWN_ENV=1` overrides, for
/// the case where an unrelated `AY_*` really is set on purpose.
fn audit_environment() -> bool {
    let audit = ay_milp::env_audit();
    for name in &audit.unknown {
        eprintln!(
            "ay-milp: ERROR: {name} is set but NO code reads it. If this is a typo, this run would \
             measure the wrong arm and record the result as a finding. \
             `ay-milp knobs --list` prints every name this build reads."
        );
    }
    for name in &audit.dead {
        eprintln!(
            "ay-milp: ERROR: {name} is set but is DEAD (mentioned in source, never read). It has \
             no effect, so this run would not be the configuration you asked for."
        );
    }
    for (name, flag) in &audit.deprecated {
        eprintln!("ay-milp: note: {name} is deprecated, use `{flag}` (the env name still works)");
    }
    if audit.is_fatal() {
        eprintln!(
            "ay-milp: refusing to run under an environment that does not mean what it says. \
             Set {}=1 to proceed anyway.",
            ay_milp::ALLOW_UNKNOWN_ENV
        );
        return false;
    }
    true
}

/// Read a flag, falling back to a deprecated env alias. The FLAG WINS.
fn flag_or_env(flags: &Flags, flag: &str, env: &str) -> Option<String> {
    flags.get(flag).cloned().or_else(|| std::env::var(env).ok())
}

fn die(msg: &str) -> ExitCode {
    eprintln!("ay-milp: {msg}");
    ExitCode::from(2)
}

// ---------------------------------------------------------------------------
// solve
// ---------------------------------------------------------------------------

/// The evidence posture. Three-valued, because the boolean is unusable:
/// `require_certificates: true` erases 4 of 4 measured verdicts on this corpus
/// at ZERO time saving, since the flag is a post-hoc verdict FILTER, not a work
/// switch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Require {
    /// Today's default: report whatever the engine warrants.
    None,
    /// A verdict must carry a primal witness that re-checks. Already true on
    /// every measured verdict; this makes it CONTRACTUAL. The new default.
    Witness,
    /// Every claim must be SUCCINCT — i.e. `require_certificates: true`.
    Full,
}

#[allow(clippy::too_many_lines)]
fn cmd_solve(args: &[String]) -> ExitCode {
    // The engine switches PLUS this command's own three. An unknown `--flag`
    // is refused here rather than parsed into silence (see `Flags::parse`).
    let mut switches = engine_flags::switch_flags();
    switches.extend([
        "no-emit-cert",
        "no-opt-tree",
        "deterministic",
        "no-deterministic",
        // DIAGNOSTIC ONLY (`--phase-ledger`): one stderr line attributing this
        // process's wall to the phases OUTSIDE the search, so "ay's fixed
        // per-solve cost" stops being a regression intercept and becomes a
        // measured sum. Reporting only; no phase is skipped, reordered, or
        // budgeted by it, and every verdict is byte-identical with it on.
        "phase-ledger",
    ]);
    let flags = match Flags::parse(args, engine_flags::VALUE_FLAGS, &switches) {
        Ok(f) => f,
        Err(e) => return die(&e),
    };
    let Some(path) = flags.positional.first().cloned() else {
        return die("solve needs a model file");
    };
    // `solve <file> <secs>` is the documented shape; anything past it was
    // silently ignored, which is how a misspelled flag's VALUE used to ride
    // through as a positional and be mistaken for an argument.
    if let Some(extra) = flags.positional.get(2) {
        return die(&format!(
            "unexpected argument `{extra}`: solve takes <file.mps[.gz]> [seconds] and flags"
        ));
    }
    if let Some(secs) = flags.positional.get(1) {
        if secs.parse::<f64>().is_err() {
            return die(&format!(
                "second argument `{secs}` is not a number of seconds \
                 (use --time-limit <secs>, or a flag it belongs to)"
            ));
        }
    }
    // Positional seconds remain accepted: `mps_solve <file> <secs>` is how every
    // measurement script in the journal invokes the solver.
    let secs: f64 = flags
        .get("time-limit")
        .and_then(|s| s.parse().ok())
        .or_else(|| flags.positional.get(1).and_then(|s| s.parse().ok()))
        .unwrap_or(60.0);

    let require = match flags.get("require").map(String::as_str) {
        None | Some("witness") => Require::Witness,
        Some("none") => Require::None,
        Some("full") => Require::Full,
        Some(other) => return die(&format!("--require {other}: expected none|witness|full")),
    };

    let ledger = flags.has("phase-ledger");
    let t_dispatch = Instant::now();

    let t_ph = Instant::now();
    let text = match read_maybe_gz(&path) {
        Ok(t) => t,
        Err(e) => return die(&format!("cannot read {path}: {e}")),
    };
    let ph_read = t_ph.elapsed();
    let t_ph = Instant::now();
    let p = match ay_milp::read_mps(&text) {
        Ok(p) => p,
        Err(e) => {
            println!("PARSE_ERROR {e}");
            return ExitCode::from(3);
        }
    };
    let ph_parse = t_ph.elapsed();
    let t_ph = Instant::now();
    report_shape(&p);
    let ph_shape = t_ph.elapsed();

    // Full posture is adjudicated after solving, claim by claim.  In
    // particular, an integral model with a nonzero objective may still be
    // infeasible and carry a complete Farkas/tree/PB refutation.  Pre-refusing
    // that model shape would discard a proof before learning which claim the
    // solve actually needs to make.

    let opts = match solve_options::from_flags(&flags, require, secs) {
        Ok(opts) => opts,
        Err(message) => return die(&message),
    };

    let t_ph = Instant::now();
    let col_names = p.col_names.clone();
    let obj_scale = p.obj_scale.clone();
    let mut s = match BabSession::new(p.model, &opts) {
        Ok(s) => s,
        Err(e) => {
            println!("SETUP_ERROR {e:?} - -");
            return ExitCode::from(4);
        }
    };
    let ph_session = t_ph.elapsed();
    if let Some(seedf) = flags.get("seed-solution").cloned() {
        match std::fs::read_to_string(&seedf) {
            Ok(text) => {
                let idx = name_index(&col_names);
                let mut vals = vec![0.0f64; s.model().num_cols()];
                let mut hits = 0usize;
                for line in text.lines() {
                    let f: Vec<&str> = line.split_whitespace().collect();
                    let [nm, v] = f[..] else { continue };
                    if let (Some(&j), Ok(x)) = (idx.get(nm), v.parse::<f64>()) {
                        vals[j] = x;
                        hits += 1;
                    }
                }
                eprintln!("seed: loaded {hits} column values from {seedf}");
                if hits > 0 {
                    s.seed_incumbent(&vals);
                }
            }
            Err(e) => return die(&format!("cannot read {seedf}: {e}")),
        }
    }

    let t0 = Instant::now();
    let out = s.check();
    let dt = t0.elapsed().as_secs_f64();
    let nodes = ay_milp::nodes_explored();

    let outcome = match out {
        Ok(o) => o,
        Err(e) => {
            println!("ERROR {e:?} {dt:.3} {nodes}");
            return ExitCode::from(4);
        }
    };

    // BATTERY 1 — ALWAYS EMIT. Default the certificate path to `<input>.ayc` on
    // every verdict-bearing outcome. Measured witness-serialisation cost:
    // markshare1 487 B / 16 us; blend2 3573 B / 25 us; qiu (840 cols) 7931 B /
    // 53 us against a 46.7 s solve — 1.1e-4 %. Free.
    let cert_path = if flags.has("no-emit-cert") {
        None
    } else {
        Some(
            flags
                .get("emit-cert")
                .cloned()
                .unwrap_or_else(|| format!("{path}.ayc")),
        )
    };
    let max_bytes = match flags.get("emit-cert-max-bytes") {
        Some(v) => match v.parse::<usize>() {
            Ok(n) => Some(n),
            Err(_) => return die("--emit-cert-max-bytes needs an integer"),
        },
        None => None,
    };
    // THE DUAL HALF OF AN `Optimal`. Derived here, AFTER the verdict, by an
    // independent certifying descent over the caller's model — it consumes only
    // `value` and `model_values` and re-checks both, so it cannot influence what
    // the solver answered. A budget overrun yields `None` and the claim degrades
    // to `NONE` exactly as it did before this existed; nothing is ever asserted
    // that could not be re-derived.
    // Reported on the EXISTING `certificate:` line rather than its own, so the
    // diagnostic costs no new stderr site.
    let mut opt_tree_note = String::new();
    let mut ph_opt_tree = Duration::ZERO;
    let opt_tree = if flags.has("no-opt-tree") || cert_path.is_none() {
        None
    } else {
        // THE BUDGET IS WORK; THE CLOCK IS A NET. `--opt-tree-secs` defaulted
        // to 5 and was the bound that actually fired — 136 of 164 derivations
        // over 41 OPTIMAL instances declined on it and ZERO on the leaf cap —
        // which made the emitted certificate a function of machine load.
        // Measured on `08af5e9a7`: `f2gap40400` certified 509 leaves /
        // 10,068,501 bytes / `verify` exit 0 on 4 of 4 reps at load ~70, and
        // declined at 350 / 311 / 304 / 320 leaves on 4 of 4 with the same
        // binary and input under deliberate contention. Same verdict, four
        // different certificates.
        let secs = match flags.get("opt-tree-secs") {
            Some(v) => match v.parse::<f64>() {
                Ok(x) if x >= 0.0 => x,
                _ => return die("--opt-tree-secs needs a non-negative number"),
            },
            None => OPT_TREE_BACKSTOP_SECS,
        };
        let work = match flags.get("opt-tree-work") {
            Some(v) => match v.parse::<u64>() {
                Ok(n) => n,
                Err(_) => return die("--opt-tree-work needs a non-negative integer"),
            },
            None => default_opt_tree_work(s.model()),
        };
        let leaves = match flags.get("opt-tree-leaves") {
            Some(v) => match v.parse::<usize>() {
                Ok(n) => n,
                Err(_) => return die("--opt-tree-leaves needs an integer"),
            },
            None => OPT_TREE_LEAVES,
        };
        // THE SIZE DIAL, and the reason it is a dial and not a constant is that
        // it is the one setting on this feature that trades an artifact's SIZE
        // against the work spent producing it. `0` restores the lossless
        // `f64 -> BigRational` conversion the feature shipped with. It cannot
        // trade away validity: weak duality holds for ANY dual vector, so a
        // coarser one still yields a valid bound, and every leaf is re-verified
        // against the caller's model before it enters the tree.
        let grid = match flags.get("opt-tree-grid") {
            Some(v) => match v.parse::<u32>() {
                Ok(0) => None,
                Ok(n) if n <= 60 => Some(n),
                _ => return die("--opt-tree-grid needs an integer in 0..=60"),
            },
            None => ay_milp::OptimalityTreeBudget::new(1).dual_grid_bits,
        };
        match &outcome {
            Outcome::Optimal {
                value,
                model_values,
                ..
            } if leaves > 0 => {
                let t = Instant::now();
                let budget = ay_milp::OptimalityTreeBudget::new(leaves)
                    .with_work(work)
                    .with_dual_grid_bits(grid)
                    .with_deadline(
                        (secs > 0.0).then(|| Instant::now() + Duration::from_secs_f64(secs)),
                    );
                let (derived, report) = ay_milp::derive_optimality_tree_reported(
                    s.model(),
                    value,
                    model_values,
                    &budget,
                );
                // "declined (budget or model out of reach)" was ONE message for
                // at least three unrelated events. Name the one that fired, and
                // say what it cost: the difference between `deadline` and
                // `unbounded-leaf` is the difference between "raise the budget"
                // and "never spend a second here again".
                opt_tree_note = format!(
                    ", optimality-tree {} in {:.3} s",
                    derived.as_ref().map_or_else(
                        || {
                            format!(
                                "declined ({}{}; {} leaves, depth {}, {} float + {} rim LPs, \
                                 work {}/{}, root-gap {})",
                                report
                                    .decline
                                    .map_or("unknown", ay_milp::OptTreeDecline::tag),
                                // The terminal reason is the LAST one raised, so a
                                // descent that abandoned a 512-deep subtree, or
                                // tripped the leaf cap, and then spent the rest of
                                // its budget in the exact rim says only `work-cap`.
                                // Say all three: one is a budget the caller can
                                // move, one is an artifact bound it can move
                                // separately, and one is a shape it cannot.
                                {
                                    let mut extra = String::new();
                                    if report.depth_capped > 0 {
                                        extra.push_str(&format!(
                                            " + {} at depth-cap",
                                            report.depth_capped
                                        ));
                                    }
                                    if report.leaf_capped > 0 {
                                        extra.push_str(&format!(
                                            " + {} at leaf-cap",
                                            report.leaf_capped
                                        ));
                                    }
                                    extra
                                },
                                report.leaves,
                                report.max_depth,
                                report.float_solves,
                                report.rim_solves,
                                report.work,
                                work,
                                report
                                    .root_gap_rel
                                    .map_or_else(|| "n/a".to_string(), |g| format!("{g:.6}"))
                            )
                        },
                        // WORK IS ON THE SUCCESS LINE TOO. It is the only number
                        // here that says how close this derivation came to the
                        // budget, and a harness that wants to know whether a
                        // certificate is at risk of being lost to a future
                        // budget change has nowhere else to read it.
                        // `grid` and `grid-fallbacks` ride here for the mirror
                        // reason: a fallback count near `by bound` means the
                        // coarse rung is closing nothing and only costing
                        // retries, and neither number can be read off the file.
                        |c| format!(
                            "{} leaves = {} by bound + {} empty (work {}/{}, root-gap {}, \
                             grid {}, {} grid-fallbacks)",
                            c.num_leaves(),
                            c.num_dominated_leaves(),
                            c.num_leaves() - c.num_dominated_leaves(),
                            report.work,
                            work,
                            report
                                .root_gap_rel
                                .map_or_else(|| "n/a".to_string(), |g| format!("{g:.6}")),
                            grid.map_or_else(|| "off".to_string(), |b| format!("2^-{b}")),
                            report.grid_fallbacks,
                        )
                    ),
                    t.elapsed().as_secs_f64()
                );
                ph_opt_tree = t.elapsed();
                derived
            }
            _ => None,
        }
    };

    let mut ph_cert = Duration::ZERO;
    if let Some(cp) = &cert_path {
        let t = Instant::now();
        let ctx = cert_io::EmitCtx {
            model: s.model(),
            model_text: &text,
            col_names: &col_names,
            obj_scale: &obj_scale,
            provenance: &provenance(),
            replay_claims: s.replay_claims(),
            affine_aggregation_certificate: s.affine_aggregation_certificate(),
            parity_infeasibility_certificate: s.parity_infeasibility_certificate(),
            sat_relu_infeasibility_certificate: s.sat_relu_infeasibility_certificate(),
            network_design_infeasibility_certificate: s.network_design_infeasibility_certificate(),
            network_design_optimality_certificate: s.network_design_optimality_certificate(),
            block_angular_optimality_certificate: s.block_angular_optimality_certificate(),
            milp_optimality_tree_certificate: opt_tree.as_ref(),
            single_machine_scheduling_optimality_certificate: s
                .single_machine_scheduling_optimality_certificate(),
            single_row_dp_infeasibility_certificate: s.single_row_dp_infeasibility_certificate(),
            multi_row_bdd_infeasibility_certificate: s.multi_row_bdd_infeasibility_certificate(),
            open_domain_single_row_dp_infeasibility_certificate: s
                .open_domain_single_row_dp_infeasibility_certificate(),
            open_domain_multi_row_bdd_infeasibility_certificate: s
                .open_domain_multi_row_bdd_infeasibility_certificate(),
            open_domain_hybrid_pb_lp_infeasibility_certificate: s
                .open_domain_hybrid_pb_lp_infeasibility_certificate(),
            open_domain_hybrid_integer_lift_infeasibility_certificate: s
                .open_domain_hybrid_integer_lift_infeasibility_certificate(),
            hybrid_pb_lp_infeasibility_certificate: s.hybrid_pb_lp_infeasibility_certificate(),
            hybrid_integer_lift_infeasibility_certificate: s
                .hybrid_integer_lift_infeasibility_certificate(),
            max_bytes,
        };
        let ayc = cert_io::emit(&ctx, &outcome);
        let bytes = ayc.len();
        match std::fs::write(cp, ayc.as_bytes()) {
            Ok(()) => eprintln!(
                "certificate: {cp} ({bytes} bytes, {} us){opt_tree_note}",
                t.elapsed().as_micros()
            ),
            Err(e) => eprintln!("ay-milp: WARNING: cannot write {cp}: {e}"),
        }
        ph_cert = t.elapsed();
    }

    // --emit-witness works on EVERY verdict that has a point, which is the whole
    // point: `AY_DUMP_SOL` only ever fired on `Feasible`.
    let witness_path = flags.get("emit-witness").cloned(); // B22: env fallback retired.
    let wfmt = flags.get("witness-format").map_or_else(
        || {
            // The env alias keeps its historical `name <decimal>` shape so the
            // journal's comparison scripts read it unchanged.
            if flags.get("emit-witness").is_none() {
                "sol"
            } else {
                "rational"
            }
        },
        String::as_str,
    );
    if let Some(wp) = &witness_path {
        if let Some(x) = witness_of(&outcome) {
            match write_witness(wp, x, &col_names, wfmt) {
                Ok(()) => eprintln!("witness: {wp} ({} columns, format {wfmt})", x.len()),
                Err(e) => eprintln!("ay-milp: WARNING: cannot write {wp}: {e}"),
            }
        } else {
            eprintln!("witness: none — verdict carries no point");
        }
    }

    // BATTERY 4 — `--require witness` as the default posture. The engine's own
    // The session boundary validates any published witness; this makes the
    // guarantee CONTRACTUAL by re-checking here independently and failing the
    // run rather than printing an unbacked verdict.
    let t_ph = Instant::now();
    let mut ph_require = Duration::ZERO;
    if require != Require::None {
        if let Some(x) = witness_of(&outcome) {
            if let Err(v) = s.model().check_point(x) {
                eprintln!(
                    "ay-milp: --require witness FAILED: the verdict's point is infeasible ({v:?})"
                );
                return ExitCode::from(5);
            }
        } else if outcome.is_sat() {
            eprintln!("ay-milp: --require witness FAILED: a sat verdict carries no point");
            return ExitCode::from(5);
        }
        ph_require = t_ph.elapsed();
    }

    // THE FIXED PER-SOLVE COST, AS A SUM RATHER THAN A REGRESSION INTERCEPT.
    //
    // Least squares over 37 both-proved instances put ay at `1.492 s +
    // 26.51 us/node` against Gurobi's `0.076 s + 49.48 us/node` and the
    // campaign read the intercept ratio as a real 19.6x fixed-cost gap. It is
    // not one: ay finishes stein9inf in 12 ms wall, which a 1.49 s fixed cost
    // makes impossible. The intercept is what an unweighted two-parameter fit
    // does with a per-node cost that spans four orders of magnitude across the
    // corpus — it absorbs residual, and it is smaller than the residual SD.
    //
    // So the fixed cost has to be MEASURED. Every phase outside `check()` is
    // timed above and printed here alongside `solve`, and the caller differences
    // `total` against its own wall clock to recover the exec chain (`arm`'s
    // re-exec through `taskpolicy` costs a second process image) plus dyld and
    // the Rust prologue. `resid` is whatever this function did that no phase
    // claimed; it is printed rather than absorbed, because a decomposition with
    // an unattributed remainder is not a decomposition.
    if ledger {
        let in_main = MAIN_T0.get().map_or(Duration::ZERO, Instant::elapsed);
        let dispatch = MAIN_T0.get().map_or(Duration::ZERO, |t0| {
            t_dispatch.saturating_duration_since(*t0)
        });
        let named = ph_read
            + ph_parse
            + ph_shape
            + ph_session
            + Duration::from_secs_f64(dt)
            + ph_opt_tree
            + ph_cert
            + ph_require
            + dispatch;
        let us = |d: Duration| d.as_micros();
        eprintln!(
            "phase-ledger: dispatch={} read={} parse={} shape={} session={} solve={} \
             opt_tree={} cert={} require={} resid={} in_main={} (us)",
            us(dispatch),
            us(ph_read),
            us(ph_parse),
            us(ph_shape),
            us(ph_session),
            (dt * 1e6) as u128,
            us(ph_opt_tree),
            us(ph_cert),
            us(ph_require),
            us(in_main.saturating_sub(named)),
            us(in_main),
        );
    }

    let json = flags.get("format").map(String::as_str) == Some("json");
    let (status, value, detail) = verdict_line(&outcome, s.model(), &obj_scale, dt, nodes);
    // THE RIGOROUS DUAL BOUND, WHICH THIS BINARY USED TO DROP ON THE FLOOR.
    //
    // `Outcome::Feasible` has always carried `dual_bound`, and `verdict_line`
    // destructured it away — so `ay-milp solve` printed `FEASIBLE <value>` and a
    // caller could not tell "within 2% of optimal" from "no idea". For the
    // consumer this solver exists for, that difference IS the answer. The bound
    // is `None` unless the session's own `validate_witnesses` accepted it, and
    // it is nulled outright on inexact-coefficient models, so `null`/`-` here
    // means "no rigorous claim", never "not printed".
    //
    // ⚠ `Outcome::Bound` MUST BE LISTED HERE. It is the outcome the tree emits
    // when it stops with no incumbent but a rigorous frontier bound — i.e.
    // exactly the case this reporting exists for — and a `_ => None` arm nulls
    // the field on precisely those runs (measured: 40 of 117 mid-tier solves).
    // It also matters that `value` and `dual_bound` are then BOTH populated and
    // sit on OPPOSITE SIDES of the optimum: for `FEASIBLE`, `value` is the
    // primal incumbent (an upper bound on a Minimize); for `BOUND` there is no
    // incumbent and `value` is the dual bound itself (a lower bound). A reader
    // that keys on the field name rather than on `status` will read one for the
    // other, so both are emitted and `status` is the discriminator.
    //
    // Scaled by `obj_scale` exactly as the value is: the reader integralises the
    // objective and that scale is undone HERE, outside the engine. `obj_scale`
    // is positive by construction, so the bound's direction survives the divide.
    let bound = match &outcome {
        Outcome::Feasible { dual_bound, .. } => {
            dual_bound.as_ref().map(|b| decimal(&(b / &obj_scale)))
        }
        Outcome::Bound {
            dual_bound,
            rigorous,
        } => {
            // A non-rigorous bound is advice, and this field is documented as a
            // rigorous claim. Emitting a heuristic value here would make the
            // field mean two different things depending on a flag the caller
            // cannot see, so a non-rigorous bound is withheld like any other.
            rigorous.then(|| decimal(&(dual_bound / &obj_scale)))
        }
        _ => None,
    };
    if json {
        println!(
            "{}",
            solve_json_line(
                &status,
                value.as_deref(),
                bound.as_deref(),
                detail.as_deref(),
                dt,
                nodes,
                ay_milp::root_nodes_explored(),
                ay_milp::submip_nodes_explored(),
                s.replay_claims().len(),
            )
        );
    } else {
        // The line shape is FROZEN: the journal's measurement scripts read it.
        // `status` and `detail` were one string before they were split for the
        // JSON lane, and re-joining with a space here reproduces it byte for
        // byte (`UNKNOWN SolverIncomplete { detail: "..." } - 12.102 1`).
        println!(
            "{status}{} {} {dt:.3} {nodes}{}",
            detail.map_or(String::new(), |d| format!(" {d}")),
            value.as_deref().unwrap_or("-"),
            bound.map_or(String::new(), |b| format!(" bound={b}"))
        );
    }
    for rc in s.replay_claims() {
        eprintln!(
            "replay claim: {} — NOT certified. Re-verification means re-running the solver; tcb {}",
            rc.claim, rc.tcb
        );
    }
    if require == Require::Full
        && matches!(
            outcome,
            Outcome::Unknown {
                reason: UnknownReason::CertificateUnavailable
            }
        )
    {
        eprintln!(
            "ay-milp: --require full REFUSED this verdict: no complete independently checkable \
             evidence was produced"
        );
        return ExitCode::from(2);
    }
    ExitCode::SUCCESS
}

fn witness_of(o: &Outcome) -> Option<&[BigRational]> {
    match o {
        Outcome::Optimal { model_values, .. } | Outcome::Feasible { model_values, .. } => {
            Some(model_values)
        }
        _ => None,
    }
}

/// The verdict as `(status, value, detail)`.
///
/// ⚠ `status` IS A BARE TOKEN AND MUST STAY ONE. It used to be
/// `format!("UNKNOWN {reason:?}")` for `Unknown` and `format!("OTHER {other:?}")`
/// for a future variant, and that string went into `--format json` as a JSON
/// string body — so `UnknownReason::SolverIncomplete { detail: "..." }`, whose
/// `Debug` embeds double quotes, closed the `"status"` literal early and the
/// whole line stopped being JSON. A consumer therefore hit a parse error on
/// exactly the runs where the solver had the least to say.
///
/// The `Debug` payload now rides in its own `detail`, which `solve_json_line`
/// escapes. Splitting rather than escaping in place keeps `status` an
/// ENUMERABLE discriminator, which is what the comment at the JSON call site
/// already claimed it was; a consumer can match `"UNKNOWN"` instead of
/// prefix-matching a `Debug` blob. Nothing in this repo or in ny (which links
/// the crate in-process and never shells out) parses this line, and every
/// status whose shape changes was unparseable before, so there is no consumer
/// to break.
fn verdict_line(
    o: &Outcome,
    model: &ay_milp::Model,
    obj_scale: &BigRational,
    _dt: f64,
    _nodes: u64,
) -> (String, Option<String>, Option<String>) {
    match o {
        Outcome::Optimal { value, .. } => {
            ("OPTIMAL".into(), Some(decimal(&(value / obj_scale))), None)
        }
        Outcome::Feasible { model_values, .. } => {
            let v = model.objective_value_at(model_values);
            ("FEASIBLE".into(), Some(decimal(&(&v / obj_scale))), None)
        }
        Outcome::Infeasible { .. } => ("INFEASIBLE".into(), None, None),
        Outcome::Unbounded => ("UNBOUNDED".into(), None, None),
        Outcome::Bound { dual_bound, .. } => (
            "BOUND".into(),
            Some(decimal(&(dual_bound / obj_scale))),
            None,
        ),
        // `Outcome` and `UnknownReason` are `#[non_exhaustive]`, so this binary
        // is a different crate and cannot match them exhaustively; the payload
        // arms below are the two that carry free text.
        Outcome::Unknown { reason } => ("UNKNOWN".into(), None, Some(format!("{reason:?}"))),
        other => ("OTHER".into(), None, Some(format!("{other:?}"))),
    }
}

/// The one `--format json` line, so the test exercises the real format string.
///
/// `value` and `dual_bound` are pre-rendered JSON numbers (or `None` → `null`);
/// `status` and `detail` are free text and go through [`json_escape`].
///
/// `nodes` KEEPS ITS MEANING — every node the process explored, heuristic sub-MIP
/// trees included. `root_nodes` and `submip_nodes` are an ADDITIVE decomposition
/// of it (`nodes == root_nodes + submip_nodes`), added because Gurobi's
/// `Model.NodeCount` excludes its heuristics' sub-MIPs and `root_nodes` is the
/// field that compares to it. Keys are added, never redefined or reordered away:
/// this line is consumed by key, and the frozen text line above is untouched.
fn solve_json_line(
    status: &str,
    value: Option<&str>,
    dual_bound: Option<&str>,
    detail: Option<&str>,
    dt: f64,
    nodes: u64,
    root_nodes: u64,
    submip_nodes: u64,
    replay_claims: usize,
) -> String {
    format!(
        "{{\"status\":\"{}\",\"value\":{},\"dual_bound\":{},\"detail\":{},\"time\":{dt:.3},\"nodes\":{nodes},\"root_nodes\":{root_nodes},\"submip_nodes\":{submip_nodes},\"replay_claims\":{replay_claims}}}",
        json_escape(status),
        value.unwrap_or("null"),
        dual_bound.unwrap_or("null"),
        detail.map_or_else(
            || "null".to_owned(),
            |d| format!("\"{}\"", json_escape(d))
        ),
    )
}

/// Escape a string for use inside a JSON string literal (RFC 8259 §7).
///
/// ⚠ EVERY MANDATORY ESCAPE, not just the one that bites today. The quote is
/// what broke `SolverIncomplete`, but these fields carry `Debug` output over
/// solver messages and MPS names: a backslash, a newline, or a stray control
/// character would each reproduce the same defect with a smaller trigger. So:
/// `"` and `\`, the five two-character forms, and `\u00XX` for every other
/// character below U+0020. Non-ASCII UTF-8 is legal unescaped in JSON and is
/// passed through unchanged.
fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            c if u32::from(c) < 0x20 => out.push_str(&format!("\\u{:04x}", u32::from(c))),
            c => out.push(c),
        }
    }
    out
}

fn write_witness(
    path: &str,
    x: &[BigRational],
    names: &[String],
    fmt: &str,
) -> std::io::Result<()> {
    // `File` is unbuffered: writing one exact-rational line per column used to
    // issue thousands of tiny system calls on routed network models.  The
    // witness bytes and exact checker contract are unchanged; only stage the
    // complete stream through a bounded userspace buffer.
    let mut f = std::io::BufWriter::new(std::fs::File::create(path)?);
    if fmt == "ay" {
        writeln!(f, "# ay-milp witness, {} columns, exact rationals", x.len())?;
    }
    for (j, v) in x.iter().enumerate() {
        let name = names.get(j).map_or("-", String::as_str);
        match fmt {
            // Historical `AY_DUMP_SOL` shape: what every other solver prints.
            // Lossy on purpose — a comparison script reads it, not a checker.
            "sol" => writeln!(f, "{name} {}", decimal(v))?,
            "ay" => {
                write!(f, "x {j} {name} ")?;
                write_rat(&mut f, v)?;
                writeln!(f)?;
            }
            _ => {
                write!(f, "{name} ")?;
                write_rat(&mut f, v)?;
                writeln!(f)?;
            }
        }
    }
    f.flush()
}

// ---------------------------------------------------------------------------
// verify — THE INDEPENDENT CHECKER
// ---------------------------------------------------------------------------

fn cmd_verify(args: &[String]) -> ExitCode {
    let flags = match Flags::parse(args, &["model", "cert"], &["accept-replay", "exit-zero"]) {
        Ok(f) => f,
        Err(e) => return die(&e),
    };
    let Some(model_path) = flags.get("model") else {
        return die("verify needs --model <file.mps>");
    };
    let Some(cert_path) = flags.get("cert") else {
        return die("verify needs --cert <file.ayc>");
    };
    let model_text = match read_maybe_gz(model_path) {
        Ok(t) => t,
        Err(e) => return die(&format!("cannot read {model_path}: {e}")),
    };
    let cert_text = match std::fs::read_to_string(cert_path) {
        Ok(t) => t,
        Err(e) => return die(&format!("cannot read {cert_path}: {e}")),
    };

    // The checker re-parses the model itself and re-derives every number. It
    // takes NOTHING from the certificate as fact.
    let report = cert_io::check(&cert_text, &model_text);
    for n in report.notes() {
        println!("  {n}");
    }
    for c in report.claims() {
        println!(
            "  claim {:<11} {:<9} {}  {}",
            c.name(),
            c.kind().token(),
            if c.is_verified() { "ok    " } else { "NOT-OK" },
            c.detail()
        );
    }
    // THE CENSUS LINE, always printed, on every status. The aggregate word
    // answers "is this verdict proven?"; it cannot answer "which of the things
    // this certificate asserts did you re-derive?" — and on the downstream optimization consumer's captured W1
    // corpus every one of 12 SAT verdicts carried an EXACTLY CHECKED primal
    // witness under an `UNVERIFIED` word, because the dual half of an
    // `optimal` has no object in this build. A consumer reading only the word
    // threw that witness away. It now reads `CLAIMS verified=primal
    // refuted=- unbacked=dual` and can act on it.
    println!("{}", report.census());
    let replay = report
        .claims()
        .iter()
        .any(|c| c.kind() == cert_io::EvidenceKind::Replay);

    // The word VERIFIED is reserved. `--accept-replay` prints
    // ACCEPTED-ON-TRUST and still exits non-zero unless `--exit-zero` is ALSO
    // passed. Deliberately two flags: a wrapper doing `ay-milp verify && echo
    // ok` must not be able to conflate trust with proof by accident.
    //
    // `Partial` is accepted here for the same reason `Unverified` is: it is the
    // same aggregate ("nothing refuted; something has no object"), only more
    // precisely reported. It still cannot reach exit 0 without BOTH flags.
    if matches!(
        report.status(),
        cert_io::CheckStatus::Unverified | cert_io::CheckStatus::Partial
    ) && replay
        && flags.has("accept-replay")
    {
        println!("ACCEPTED-ON-TRUST (replay claims were NOT verified)");
        if flags.has("exit-zero") {
            return ExitCode::SUCCESS;
        }
        // The status's OWN code, so trusting the replay half does not erase
        // the fact that some other claim did or did not re-derive.
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        return ExitCode::from(report.status().exit_code() as u8);
    }
    println!("{}", report.status().word());
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    ExitCode::from(report.status().exit_code() as u8)
}

// ---------------------------------------------------------------------------
// check-point — the standalone primal checker, promoted to a command
// ---------------------------------------------------------------------------

struct NamedPoint {
    values: Vec<BigRational>,
    supplied: Vec<Option<BigRational>>,
    matched_lines: usize,
}

struct RepairLimits {
    time_limit_secs: f64,
    memory_budget: Option<usize>,
}

fn parse_named_point(problem: &MpsProblem, text: &str) -> NamedPoint {
    let index = name_index(&problem.col_names);
    let mut values = vec![BigRational::zero(); problem.model.num_cols()];
    let mut supplied = vec![None; problem.model.num_cols()];
    let mut matched_lines = 0;
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split_whitespace().collect();
        // Accept `name value` and `x <j> <name> <value>`. A bare value list is
        // deliberately not accepted because it is too easy to misalign.
        let (name, value) = match fields[..] {
            [name, value] | ["x", _, name, value] => (name, value),
            _ => continue,
        };
        // Parse decimal text exactly: `0.9` is nine tenths, not the nearest
        // binary floating-point value.
        let Some(value) = parse_decimal_exact(value) else {
            continue;
        };
        if let Some(&column) = index.get(name) {
            values[column] = value.clone();
            supplied[column] = Some(value);
            matched_lines += 1;
        }
    }
    NamedPoint {
        values,
        supplied,
        matched_lines,
    }
}

fn repair_limits(flags: &Flags) -> Result<RepairLimits, String> {
    let time_limit = flags
        .get("repair-time-limit")
        .map_or(Ok(10.0), |value| value.parse::<f64>())
        .ok()
        .filter(|value| value.is_finite() && *value > 0.0)
        .ok_or_else(|| "--repair-time-limit needs a positive finite number".to_owned())?;
    let memory_budget = flags
        .get("memory-budget")
        .map(|value| {
            value
                .parse::<usize>()
                .map_err(|_| "--memory-budget needs an integer".to_owned())
        })
        .transpose()?;
    Ok(RepairLimits {
        time_limit_secs: time_limit,
        memory_budget,
    })
}

fn cmd_check_point(args: &[String]) -> ExitCode {
    let flags = match Flags::parse(
        args,
        &["model", "point", "repair-time-limit", "memory-budget"],
        &["repair-continuous"],
    ) {
        Ok(f) => f,
        Err(e) => return die(&e),
    };
    let Some(model_path) = flags.get("model") else {
        return die("check-point needs --model <file.mps>");
    };
    let Some(point_path) = flags.get("point") else {
        return die("check-point needs --point <file.sol>");
    };
    let model_text = match read_maybe_gz(model_path) {
        Ok(t) => t,
        Err(e) => return die(&format!("cannot read {model_path}: {e}")),
    };
    let point_text = match std::fs::read_to_string(point_path) {
        Ok(t) => t,
        Err(e) => return die(&format!("cannot read {point_path}: {e}")),
    };
    let p = match ay_milp::read_mps(&model_text) {
        Ok(p) => p,
        Err(e) => return die(&format!("PARSE_ERROR {e}")),
    };
    let point = parse_named_point(&p, &point_text);
    println!(
        "point: {} of {} columns named",
        point.matched_lines,
        p.model.num_cols()
    );
    match p.model.check_point(&point.values) {
        Ok(()) => {
            let v = p.model.objective_value_at(&point.values);
            println!(
                "FEASIBLE  objective {} (file frame)",
                rat(&(&v / &p.obj_scale))
            );
            println!(
                "  every row, column bound and integrality constraint checked in exact rational \
                 arithmetic against the re-parsed model"
            );
            ExitCode::SUCCESS
        }
        Err(v) if flags.has("repair-continuous") => {
            let limits = match repair_limits(&flags) {
                Ok(limits) => limits,
                Err(error) => return die(&error),
            };
            println!(
                "point: decimal text failed exact checking ({v:?}); attempting continuous repair"
            );
            match repair_continuous_completion(
                &p.model,
                &point.supplied,
                Duration::from_secs_f64(limits.time_limit_secs),
                limits.memory_budget,
            ) {
                Ok(repaired) => {
                    let value = p.model.objective_value_at(&repaired);
                    println!(
                        "FEASIBLE  objective {} (file frame; continuous values exactly repaired \
                         with every integral column fixed)",
                        rat(&(&value / &p.obj_scale))
                    );
                    println!(
                        "  repaired point rechecked against every original row, column bound and \
                         integrality constraint in exact rational arithmetic"
                    );
                    ExitCode::SUCCESS
                }
                Err(detail) => {
                    println!("INFEASIBLE  original={v:?}; repair={detail}");
                    ExitCode::from(20)
                }
            }
        }
        Err(v) => {
            println!("INFEASIBLE  {v:?}");
            ExitCode::from(20)
        }
    }
}

/// Recover an exact continuous completion of an external solver's rounded
/// point while preserving its entire integer assignment.
///
/// Text solution formats cannot, in general, print a rational LP vertex
/// exactly: even `1/3` is necessarily rounded.  Treating the rounded decimal as
/// the point would reject valid reference solutions; accepting it within a
/// tolerance would weaken this command's exact-checking contract.  The safe
/// bridge is to pin every integral column to the external solver's intended
/// integer value, solve only the remaining continuous completion, and then
/// check the returned rational point against the untouched source model.  The
/// completion is checker work, not solver timing, and failure remains a hard
/// rejection.
fn repair_continuous_completion(
    original: &ay_milp::Model,
    supplied: &[Option<BigRational>],
    time_limit: Duration,
    memory_budget: Option<usize>,
) -> Result<Vec<BigRational>, String> {
    if supplied.len() != original.num_cols() {
        return Err("point width does not match the model".to_owned());
    }
    let mut opts = SolveOpts::new()
        .with_time_limit(time_limit)
        .with_tree_cert_leaves(0);
    if let Some(bytes) = memory_budget {
        opts = opts.with_memory_budget(Some(bytes));
    }
    let mut session = BabSession::new(original.clone(), &opts)
        .map_err(|error| format!("repair setup failed: {error:?}"))?;
    let tolerance = BigRational::new(BigInt::from(1), BigInt::from(1_000_000));
    for column in 0..original.num_cols() {
        let handle = original
            .col_at(column)
            .ok_or_else(|| format!("column {column} disappeared during repair setup"))?;
        if !original.col_kind(handle).is_integral() {
            continue;
        }
        let value = supplied[column]
            .as_ref()
            .ok_or_else(|| format!("integral column {column} was not named in the point"))?;
        let truncated = value.to_integer();
        let remainder = value - BigRational::from_integer(truncated.clone());
        let half = BigRational::new(BigInt::one(), BigInt::from(2));
        let intended_integer = if remainder >= half {
            truncated + BigInt::one()
        } else if remainder <= -half {
            truncated - BigInt::one()
        } else {
            truncated
        };
        let intended_exact = BigRational::from_integer(intended_integer.clone());
        if (value - &intended_exact).abs() > tolerance {
            return Err(format!(
                "integral column {column} value {value} is not within 1e-6 of an integer"
            ));
        }
        let intended = intended_integer.to_f64().ok_or_else(|| {
            format!("integral column {column} is outside the numeric model range")
        })?;
        if BigRational::from_float(intended).as_ref() != Some(&intended_exact) {
            return Err(format!(
                "integral column {column} value {intended_integer} cannot be represented exactly \
                 by the numeric model"
            ));
        }
        session
            .fix_col(handle, intended)
            .map_err(|error| format!("cannot fix integral column {column}: {error:?}"))?;
    }
    let outcome = session
        .check()
        .map_err(|error| format!("continuous repair solve failed: {error:?}"))?;
    let repaired = match outcome {
        Outcome::Optimal { model_values, .. } | Outcome::Feasible { model_values, .. } => {
            model_values
        }
        other => return Err(format!("continuous repair produced {other:?}")),
    };
    original
        .check_point(&repaired)
        .map_err(|violation| format!("repaired point failed source check: {violation:?}"))?;
    Ok(repaired)
}

#[cfg(test)]
#[path = "ay_milp/point_repair_tests.rs"]
mod point_repair_tests;

// ---------------------------------------------------------------------------
// diag — the old env-var modes, as subcommands
// ---------------------------------------------------------------------------

/// `diag` modes whose lane threads a caller [`SolveOpts`], so an engine flag
/// given there actually reaches the engine.
///
/// `root-closure`, `lp-only`, `shipped-lp`, `dualfix`, and `margin-row` use
/// `_with` entries; `cross-check` and `profile` install the caller frame
/// through `check`.
///
/// `block-angular` reads no tuning knobs, so it remains excluded.
const DIAG_MODES_WITH_OPTS: &[&str] = &[
    "root-closure",
    "lp-only",
    "shipped-lp",
    "dualfix",
    "margin-row",
    "cross-check",
    "profile",
];

/// `diag`'s OWN carriers — parsed here, not by `engine_flags::apply`.
const DIAG_OWN_FLAGS: &[&str] = &["time-limit", "memory-budget", "row", "solution"];

fn parse_diag_flags(args: &[String]) -> Result<Flags, String> {
    // The accept list is `applied_flags()`, NOT `VALUE_FLAGS`: the latter also
    // carries `solve`'s own names (`--emit-cert`, `--require`, `--threads`),
    // which no diagnostic reads, and accepting one of those here would be the
    // same defect in a new place.
    //
    // The set algebra that used to be spelled out here is now
    // `engine_flags::parse_applied`, which the five measurement harnesses call
    // too — `diag` was the only surface that had it right, and a second copy
    // is a second thing to forget.
    engine_flags::parse_applied(args, DIAG_OWN_FLAGS, &[])
}

fn validate_diag_mode_flags(mode: &str, flags: &Flags) -> Result<(), String> {
    if DIAG_MODES_WITH_OPTS.contains(&mode) {
        return Ok(());
    }
    if let Some(stray) = flags
        .names_given()
        .into_iter()
        .find(|name| !DIAG_OWN_FLAGS.contains(name))
    {
        return Err(format!(
            "`diag {mode}` threads no SolveOpts, so `--{stray}` would have been parsed \
             and IGNORED — REFUSED rather than measured under a flag that does nothing. \
             Engine flags apply to: {}.",
            DIAG_MODES_WITH_OPTS.join(", ")
        ));
    }
    Ok(())
}

fn diag_options(flags: &Flags, secs: f64) -> Result<SolveOpts, String> {
    engine_flags::apply(
        flags,
        SolveOpts::new().with_time_limit(Duration::from_secs_f64(secs)),
    )
    .map_err(|error| format!("bad engine flag: {error}"))
}

fn run_diag_root_closure(p: &MpsProblem, secs: f64, opts: &SolveOpts) -> ExitCode {
    let line = ay_milp::diag_root_closure_with(&p.model, secs, opts);
    // The diagnostic reports in the model's sense/offset frame; what it cannot
    // undo is the reader's integralising objective scale.
    let scale = p.obj_scale.to_f64().unwrap_or(1.0);
    let rescaled = line
        .split_whitespace()
        .map(|token| match token.split_once('=') {
            Some((key @ ("bound_lp" | "bound_cut" | "gain"), value)) => {
                let value: f64 = value.parse().unwrap_or(f64::NAN);
                format!("{key}={}", value / scale)
            }
            _ => token.to_string(),
        })
        .collect::<Vec<_>>()
        .join(" ");
    println!("{rescaled}");
    ExitCode::SUCCESS
}

fn run_diag_profile(model: ay_milp::Model, opts: &SolveOpts) -> ExitCode {
    let mut session = match BabSession::new(model, opts) {
        Ok(session) => session,
        Err(error) => return die(&format!("{error:?}")),
    };
    let started = Instant::now();
    let outcome = session.check();
    eprintln!(
        "profile: {:?} in {:.3}s",
        outcome.map(|value| value.is_sat()),
        started.elapsed().as_secs_f64()
    );
    print_profiles();
    ExitCode::SUCCESS
}

fn run_diag_block_angular(flags: &Flags, p: &MpsProblem, secs: f64) -> ExitCode {
    let memory_budget = match flags.get("memory-budget") {
        Some(value) => match value.parse::<usize>() {
            Ok(value) => Some(value),
            Err(_) => return die("--memory-budget needs an integer"),
        },
        None => None,
    };
    println!(
        "{}",
        ay_milp::diag_block_angular(&p.model, secs, memory_budget)
    );
    ExitCode::SUCCESS
}

struct DiagRequest {
    flags: Flags,
    mode: String,
    secs: f64,
    opts: SolveOpts,
    problem: MpsProblem,
}

fn prepare_diag(args: &[String]) -> Result<DiagRequest, String> {
    let flags = parse_diag_flags(args)?;
    let mode = flags.positional.first().cloned().ok_or_else(|| {
        "diag needs a mode (root-closure|lp-only|shipped-lp|dualfix|block-angular|margin-row|cross-check|profile)"
            .to_owned()
    })?;
    validate_diag_mode_flags(&mode, &flags)?;
    let path = flags
        .positional
        .get(1)
        .cloned()
        .ok_or_else(|| "diag needs a model file".to_owned())?;
    let secs = flags
        .get("time-limit")
        .and_then(|value| value.parse().ok())
        .or_else(|| flags.positional.get(2).and_then(|value| value.parse().ok()))
        .unwrap_or(60.0);
    let opts = diag_options(&flags, secs)?;
    let text = read_maybe_gz(&path).map_err(|error| format!("cannot read {path}: {error}"))?;
    let problem = ay_milp::read_mps(&text).map_err(|error| format!("PARSE_ERROR {error}"))?;
    Ok(DiagRequest {
        flags,
        mode,
        secs,
        opts,
        problem,
    })
}

fn cmd_diag(args: &[String]) -> ExitCode {
    let request = match prepare_diag(args) {
        Ok(request) => request,
        Err(error) => return die(&error),
    };
    let DiagRequest {
        flags,
        mode,
        secs,
        opts,
        problem: p,
    } = request;
    report_shape(&p);
    match mode.as_str() {
        "root-closure" => run_diag_root_closure(&p, secs, &opts),
        "lp-only" => {
            // `units_clause` is APPENDED, not printed under: the value on this line
            // is the scaled model's, and the factor has to travel with it.
            eprintln!(
                "{}{}",
                ay_milp::diag_float_lp_with(&p.model, secs, &opts),
                p.units_clause()
            );
            print_profiles();
            ExitCode::SUCCESS
        }
        // THE SHIPPED LANE, on the same subject as `lp-only`. `lp-only` is an
        // iteration-economics scaffold: one cold walk, no ladder, nothing
        // certified. Its status and objective have twice been quoted as solver
        // behaviour and been wrong both times, so the diagnostic that answers
        // "what does the solver actually do with this LP" now exists as its own
        // mode rather than as a footnote nobody reads.
        "shipped-lp" => {
            // Same append, and it matters MORE here: this line says
            // `certified=true`, so its value reads as adjudicated truth. It is —
            // in the scaled model's units.
            eprintln!(
                "{}{}",
                ay_milp::diag_shipped_float_lp(&p.model, secs, &opts),
                p.units_clause()
            );
            print_profiles();
            ExitCode::SUCCESS
        }
        // What DUAL FIXING does to this model, without solving it. `int_prop_only`
        // is the `DualReductions=0` arm and `int_after` the default one, both
        // measured on the same pass so the attribution needs no second run.
        "dualfix" => {
            println!("{}", ay_milp::diag_dualfix_with(&p.model, secs, &opts));
            ExitCode::SUCCESS
        }
        "block-angular" => run_diag_block_angular(&flags, &p, secs),
        "margin-row" => {
            // B22: --row is the carrier; the env fallback is retired.
            let spec = flags.get("row").cloned().unwrap_or_else(|| "last".into());
            let nrows = p.model.num_rows();
            let row_idx = if spec.eq_ignore_ascii_case("last") {
                nrows.checked_sub(1)
            } else {
                spec.parse::<usize>().ok()
            };
            let Some(row_idx) = row_idx.filter(|&i| i < nrows) else {
                return die(&format!("--row {spec}: bad row ({nrows} rows)"));
            };
            let mut m = p.model.clone();
            let row = m.row_at(row_idx).expect("in range");
            if let Err(e) = m.mark_margin_row(row) {
                return die(&format!("mark_margin_row({row_idx}): {e}"));
            }
            eprintln!("{}", ay_milp::diag_margin_reframe_with(&m, secs, &opts));
            ExitCode::SUCCESS
        }
        "cross-check" => {
            let Some(sol) = flags.get("solution").cloned() else {
                return die("diag cross-check needs --solution <path>");
            };
            let Ok(stext) = std::fs::read_to_string(&sol) else {
                return die(&format!("cannot read {sol}"));
            };
            let idx = name_index(&p.col_names);
            let mut m = p.model.clone();
            let mut pinned = 0;
            for line in stext.lines() {
                let f: Vec<&str> = line.split_whitespace().collect();
                let [nm, v] = f[..] else { continue };
                let (Some(&j), Ok(xv)) = (idx.get(nm), v.parse::<f64>()) else {
                    continue;
                };
                let c = m.col_at(j).expect("in range");
                if m.col_kind(c).is_integral() {
                    m.fix_col(c, xv.round());
                    pinned += 1;
                }
            }
            eprintln!("cross-check: pinned {pinned} integer columns to the reference solution");
            let mut s = match BabSession::new(m, &opts) {
                Ok(s) => s,
                Err(e) => return die(&format!("{e:?}")),
            };
            match s.check() {
                Ok(Outcome::Optimal { value, .. }) => eprintln!(
                    "cross-check: OPTIMAL at {} — the model HAS this solution",
                    decimal(&p.unscale(&value))
                ),
                Ok(o) => eprintln!("cross-check: {o:?}"),
                Err(e) => eprintln!("cross-check: ERROR {e:?}"),
            }
            ExitCode::SUCCESS
        }
        "profile" => run_diag_profile(p.model, &opts),
        other => die(&format!("unknown diag mode `{other}`")),
    }
}

fn print_profiles() {
    for line in [
        ay_milp::rt_profile_line(),
        ay_milp::upd_profile_line(),
        ay_milp::px_profile_line(),
        ay_milp::sb_profile_line(),
    ] {
        if !line.is_empty() {
            eprintln!("{line}");
        }
    }
}

// ---------------------------------------------------------------------------
// knobs / features / replay-claims
// ---------------------------------------------------------------------------

fn cmd_knobs(args: &[String]) -> ExitCode {
    let flags = match Flags::parse(args, &["bucket"], &["list", "audit", "deprecated"]) {
        Ok(f) => f,
        Err(e) => return die(&e),
    };
    if flags.has("audit") {
        let a = ay_milp::env_audit();
        println!("set and read:      {}", a.known.len());
        for (k, v) in &a.known {
            println!("  {k}={v}");
        }
        println!("set but UNKNOWN:   {}", a.unknown.len());
        for k in &a.unknown {
            println!("  {k}   <- nothing reads this; a typo here measures the wrong arm");
        }
        println!("set but DEAD:      {}", a.dead.len());
        for k in &a.dead {
            println!("  {k}");
        }
        return if a.unknown.is_empty() {
            ExitCode::SUCCESS
        } else {
            ExitCode::from(10)
        };
    }
    if flags.has("deprecated") {
        for d in ay_milp::DEPRECATED {
            println!("{:<32} -> {}", d.env, d.flag);
        }
        return ExitCode::SUCCESS;
    }
    let want = flags.get("bucket").cloned();
    let mut counts = std::collections::BTreeMap::new();
    for k in ay_milp::KNOBS {
        *counts.entry(k.bucket.name()).or_insert(0usize) += 1;
        if want.as_deref().is_some_and(|w| w != k.bucket.name()) {
            continue;
        }
        println!(
            "{:<40} {:<12} reads={}",
            k.name,
            k.bucket.name(),
            k.read_sites
        );
    }
    if want.is_none() {
        println!("\n{} names total:", ay_milp::KNOBS.len());
        for (b, n) in counts {
            println!("  {b:<12} {n}");
        }
    }
    ExitCode::SUCCESS
}

fn cmd_features(args: &[String]) -> ExitCode {
    let flags = match Flags::parse(args, &[], &["list"]) {
        Ok(f) => f,
        Err(e) => return die(&e),
    };
    if !flags.has("list") {
        return die("features needs --list");
    }
    println!(
        "Kill switches for shipped defaults. Each disables an optimisation that is ON by default.\n\
         These are the A/B mechanism every measured result in the journal rests on — they are \n\
         permanent, not deprecated.\n"
    );
    for k in ay_milp::KNOBS
        .iter()
        .filter(|k| k.bucket == ay_milp::Bucket::KillSwitch)
    {
        println!("  {}=1", k.name);
    }
    ExitCode::SUCCESS
}

fn cmd_replay_claims() -> ExitCode {
    println!(
        "Claims this build can reach WITHOUT an exportable certificate. Each is re-verifiable only\n\
         by re-running the solver. If this list GROWS between releases, something regressed from\n\
         provable to trusted.\n"
    );
    println!(
        "  objective-face-empty     lattice-cvp   exhaustive CVP sweep proves the objective-0 face\n\
         \x20                                      empty (optimum >= 1). Node budget 4e9; the\n\
         \x20                                      enumeration tree shape depends on a BKZ basis\n\
         \x20                                      reduced under a WALL-CLOCK budget, so a re-run on\n\
         \x20                                      another machine re-ATTEMPTS the claim rather than\n\
         \x20                                      reproducing the object.\n\
         \x20                                      tcb crates/ay-milp/src/lattice.rs"
    );
    println!(
        "  feasibility-face-empty   lattice-cvp   same sweep, feasibility model => INFEASIBLE.\n\
         \x20                                      tcb crates/ay-milp/src/lattice.rs"
    );
    println!(
        "  coset-inconsistent       lattice-hnf   exact column-HNF shows A x = b has no integer\n\
         \x20                                      solution. DETERMINISTIC, and the one claim here\n\
         \x20                                      that HAS a short certificate in theory (a rational\n\
         \x20                                      u with u'A integral and u'b non-integral). Not\n\
         \x20                                      built yet — recorded as trusted rather than\n\
         \x20                                      dressed up as proved.\n\
         \x20                                      tcb crates/ay-milp/src/lattice.rs"
    );
    println!(
        "  sat-relu-cnf-unsat       sat-relu      exact structural recovery plus CDCL refutes the\n\
         \x20                                      encoded Boolean instance. The MILP-to-CNF\n\
         \x20                                      equivalence is checked by the recognizer; normal\n\
         \x20                                      completion exports SUCCINCT sat-relu-rup. This\n\
         \x20                                      replay id now means the bounded proof path\n\
         \x20                                      declined and ordinary CDCL supplied the verdict.\n\
         \x20                                      tcb crates/ay-milp/src/sat_relu.rs +\n\
         \x20                                      crates/ay-milp/src/sat_route.rs + ay-sat"
    );
    println!(
        "  direct-cnf-unsat          direct-cnf    exact Boolean-domain and row-side recovery plus\n\
         \x20                                      CDCL refutes the recovered CNF. Every true\n\
         \x20                                      rational coefficient and bound is consumed, but\n\
         \x20                                      the reduction is not yet an exportable proof.\n\
         \x20                                      tcb crates/ay-milp/src/direct_cnf.rs +\n\
         \x20                                      crates/ay-milp/src/sat_route.rs + ay-sat"
    );
    println!(
        "  pb-projection-infeasible  single-row-dp exact rational bounded-integer projection plus\n\
         \x20                                      redundant exact subset-sum passes prove the row\n\
         \x20                                      infeasible. This replay id now means the bounded\n\
         \x20                                      reachability artifact could not be exported; a\n\
         \x20                                      normal completed artifact is SUCCINCT instead.\n\
         \x20                                      tcb crates/ay-milp/src/pb_translate.rs +\n\
         \x20                                      crates/ay-milp/src/pb_route.rs +\n\
         \x20                                      ay-pb-core/src/single_row_dp.rs"
    );
    println!(
        "  pb-projection-optimal     single-row-dp the same exact projection plus redundant exact\n\
         \x20                                      knapsack passes proves no better encoded point\n\
         \x20                                      exists; the primal remains succinctly checked.\n\
         \x20                                      tcb crates/ay-milp/src/pb_translate.rs +\n\
         \x20                                      crates/ay-milp/src/pb_route.rs +\n\
         \x20                                      ay-pb-core/src/single_row_dp.rs"
    );
    println!(
        "  pb-portfolio-projection-infeasible\n\
         \x20                            pb-portfolio exact bounded-integer projection plus bounded\n\
         \x20                                      exhaustion of AY's core PB portfolio. The\n\
         \x20                                      reduction is replay-only.\n\
         \x20                                      tcb crates/ay-milp/src/pb_translate.rs +\n\
         \x20                                      crates/ay-milp/src/pb_route.rs + ay-pb-core"
    );
    println!(
        "  pb-portfolio-projection-optimal\n\
         \x20                            pb-portfolio the same exact projection proves the compact\n\
         \x20                                      PB optimum; the primal remains succinctly checked.\n\
         \x20                                      tcb crates/ay-milp/src/pb_translate.rs +\n\
         \x20                                      crates/ay-milp/src/pb_route.rs + ay-pb-core"
    );
    println!(
        "  network-design-projection-infeasible\n\
         \x20                            network-pb  exact directed-incidence recognition plus\n\
         \x20                                      Hoffman/TU projection and bounded PB exhaustion.\n\
         \x20                                      The reduction is replay-only.\n\
         \x20                                      tcb crates/ay-milp/src/network_design_pb.rs +\n\
         \x20                                      crates/ay-milp/src/network_design_route.rs +\n\
         \x20                                      ay-pb-core"
    );
    println!(
        "  network-design-projection-optimal\n\
         \x20                            network-pb  the same exact projection plus exact rational\n\
         \x20                                      flow completion proves the original objective.\n\
         \x20                                      tcb crates/ay-milp/src/network_design_pb.rs +\n\
         \x20                                      crates/ay-milp/src/network_design_route.rs +\n\
         \x20                                      ay-pb-core"
    );
    println!(
        "  open-domain-projection-infeasible\n\
         \x20                            open-domain exact monotone existential projection onto a\n\
         \x20                                      bounded integer residual, followed by bounded\n\
         \x20                                      exact exhaustion and source-model revalidation.\n\
         \x20                                      tcb crates/ay-milp/src/open_domain.rs +\n\
         \x20                                      crates/ay-milp/src/open_domain_route.rs +\n\
         \x20                                      ay-pb-core"
    );
    println!(
        "  open-domain-cap-optimal\n\
         \x20                            open-domain a checked source incumbent induces an inclusive\n\
         \x20                                      finite objective cap; exact bounded optimization\n\
         \x20                                      and source-model replay prove the optimum.\n\
         \x20                                      tcb crates/ay-milp/src/open_domain.rs +\n\
         \x20                                      crates/ay-milp/src/open_domain_route.rs +\n\
         \x20                                      ay-pb-core"
    );
    println!(
        "  hybrid-pb-lp-infeasible  pb+lp         exact binary master exhaustion after every\n\
         \x20                                      continuous subproblem conflict is licensed by an\n\
         \x20                                      exactly rechecked Farkas/Benders row or no-good.\n\
         \x20                                      tcb crates/ay-milp/src/hybrid_pb_lp.rs +\n\
         \x20                                      crates/ay-milp/src/cert.rs + ay-pb-core"
    );
    println!(
        "  hybrid-pb-lp-optimal     pb+lp         the same decomposition proves the compact master\n\
         \x20                                      optimum and checks a continuous feasible lift at\n\
         \x20                                      that objective; exhaustion remains replay-only.\n\
         \x20                                      tcb crates/ay-milp/src/hybrid_pb_lp.rs +\n\
         \x20                                      crates/ay-milp/src/cert.rs + ay-pb-core"
    );
    ExitCode::SUCCESS
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

fn report_shape(p: &MpsProblem) {
    let (mut bin, mut int, mut con) = (0, 0, 0);
    for j in 0..p.model.num_cols() {
        let c = p.model.col_at(j).expect("in range");
        match p.model.col_kind(c) {
            ColKind::Binary => bin += 1,
            ColKind::Integer => int += 1,
            _ => con += 1,
        }
    }
    eprintln!(
        "{}: {} rows, {} cols ({bin} bin, {int} int, {con} cont), sense {:?}",
        p.name,
        p.model.num_rows(),
        p.model.num_cols(),
        p.model.sense()
    );
}

fn name_index(names: &[String]) -> std::collections::HashMap<&str, usize> {
    names
        .iter()
        .enumerate()
        .map(|(i, n)| (n.as_str(), i))
        .collect()
}

fn provenance() -> String {
    let epoch = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_secs());
    format!(
        "host={}-{} epoch={epoch}",
        std::env::consts::OS,
        std::env::consts::ARCH
    )
}

/// A rational as a decimal, which is what every other solver prints.
fn decimal(v: &BigRational) -> String {
    v.to_f64().map_or_else(|| v.to_string(), |f| format!("{f}"))
}

/// A rational in canonical wire form.
fn rat(v: &BigRational) -> String {
    if v.denom().is_one() {
        v.numer().to_string()
    } else {
        format!("{}/{}", v.numer(), v.denom())
    }
}

/// Stream a rational in the same canonical wire form as [`rat`] without
/// allocating an intermediate `String` for every witness column.
fn write_rat(out: &mut impl std::io::Write, v: &BigRational) -> std::io::Result<()> {
    if v.denom().is_one() {
        write!(out, "{}", v.numer())
    } else {
        write!(out, "{}/{}", v.numer(), v.denom())
    }
}

/// Parse a decimal literal as an EXACT rational from its text.
///
/// `0.9` is nine tenths. Reading it as the nearest `f64` and then reasoning
/// exactly about that would adjudicate a model nobody wrote — the same trap
/// `read_mps` exists to avoid. Also accepts `num/den`.
fn parse_decimal_exact(s: &str) -> Option<BigRational> {
    let s = s.trim();
    if let Some((n, d)) = s.split_once('/') {
        let n: BigInt = n.trim().parse().ok()?;
        let d: BigInt = d.trim().parse().ok()?;
        if !d.is_positive() {
            return None;
        }
        return Some(BigRational::new(n, d));
    }
    let (mant, exp) = match s.split_once(['e', 'E']) {
        Some((m, e)) => (m, e.parse::<i32>().ok()?),
        None => (s, 0),
    };
    let (int_part, frac) = match mant.split_once('.') {
        Some((i, f)) => (i, f),
        None => (mant, ""),
    };
    if frac.chars().any(|c| !c.is_ascii_digit()) {
        return None;
    }
    let digits = format!("{int_part}{frac}");
    let n: BigInt = digits.parse().ok()?;
    let scale = i32::try_from(frac.len()).ok()? - exp;
    let ten = BigInt::from(10);
    Some(if scale >= 0 {
        BigRational::new(n, ten.pow(u32::try_from(scale).ok()?))
    } else {
        BigRational::from_integer(n * ten.pow(u32::try_from(-scale).ok()?))
    })
}

/// MIPLIB ships `.mps.gz`. Decompressing through the system `gzip` keeps the
/// engine crate free of a compression dependency.
fn read_maybe_gz(path: &str) -> std::io::Result<String> {
    if !path
        .get(path.len().saturating_sub(3)..)
        .is_some_and(|extension| extension.eq_ignore_ascii_case(".gz"))
    {
        return std::fs::read_to_string(path);
    }
    let out = std::process::Command::new("gzip")
        .args(["-dc", path])
        .output()?;
    if !out.status.success() {
        return Err(std::io::Error::other(format!(
            "gzip -dc {path}: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        )));
    }
    String::from_utf8(out.stdout).map_err(std::io::Error::other)
}

// ---------------------------------------------------------------------------
// `--format json` must actually be JSON
// ---------------------------------------------------------------------------

#[cfg(test)]
#[path = "ay_milp/json_output_tests.rs"]
mod json_output_tests;
