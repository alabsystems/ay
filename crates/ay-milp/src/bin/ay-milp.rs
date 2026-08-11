// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

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

const USAGE: &str = "\
ay-milp — MILP/LP engine with certified verdicts

USAGE
  ay-milp solve <file.mps[.gz]> [options]
  ay-milp verify --model <file.mps> --cert <file.ayc> [--accept-replay] [--exit-zero]
  ay-milp check-point --model <file.mps> --point <file.sol> [--repair-continuous]
  ay-milp diag <root-closure|lp-only|dualfix|block-angular|margin-row|cross-check|profile> <file.mps> [--time-limit <sec>] [--memory-budget <bytes>]
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

fn main() -> ExitCode {
    // FIRST statement of main: arm() re-execs this process under a kernel-held
    // memory bound, so anything above it is discarded work, and it sets an env
    // var (sound only while single-threaded). See crates/ay-sys/src/govern.rs.
    ay_sys::govern::arm();

    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() || args[0] == "-h" || args[0] == "--help" {
        print!("{USAGE}");
        return ExitCode::from(if args.is_empty() { 2 } else { 0 });
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

// ---------------------------------------------------------------------------
// Argument plumbing (hand-rolled: this crate does not take a CLI dependency)
// ---------------------------------------------------------------------------

struct Flags {
    positional: Vec<String>,
    named: Vec<(String, String)>,
    switches: Vec<String>,
}

impl Flags {
    fn parse(args: &[String], value_flags: &[&str]) -> Result<Self, String> {
        let mut f = Flags {
            positional: Vec::new(),
            named: Vec::new(),
            switches: Vec::new(),
        };
        let mut i = 0;
        while i < args.len() {
            let a = &args[i];
            if let Some(name) = a.strip_prefix("--") {
                let (name, inline) = match name.split_once('=') {
                    Some((n, v)) => (n, Some(v.to_string())),
                    None => (name, None),
                };
                if value_flags.contains(&name) {
                    let v = match inline {
                        Some(v) => v,
                        None => {
                            i += 1;
                            args.get(i)
                                .ok_or_else(|| format!("--{name} needs a value"))?
                                .clone()
                        }
                    };
                    f.named.push((name.to_string(), v));
                } else {
                    if inline.is_some() {
                        return Err(format!("--{name} takes no value"));
                    }
                    f.switches.push(name.to_string());
                }
            } else {
                f.positional.push(a.clone());
            }
            i += 1;
        }
        Ok(f)
    }

    fn get(&self, name: &str) -> Option<&String> {
        self.named
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, v)| v)
    }

    fn has(&self, name: &str) -> bool {
        self.switches.iter().any(|s| s == name)
    }
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
    let vf = [
        "time-limit",
        "threads",
        "seed",
        "memory-budget",
        "tree-cert-leaves",
        "seed-solution",
        "require",
        "emit-cert",
        "emit-cert-max-bytes",
        "emit-witness",
        "witness-format",
        "format",
    ];
    let flags = match Flags::parse(args, &vf) {
        Ok(f) => f,
        Err(e) => return die(&e),
    };
    let Some(path) = flags.positional.first().cloned() else {
        return die("solve needs a model file");
    };
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

    let text = match read_maybe_gz(&path) {
        Ok(t) => t,
        Err(e) => return die(&format!("cannot read {path}: {e}")),
    };
    let p = match ay_milp::read_mps(&text) {
        Ok(p) => p,
        Err(e) => {
            println!("PARSE_ERROR {e}");
            return ExitCode::from(3);
        }
    };
    report_shape(&p);

    // Full posture is adjudicated after solving, claim by claim.  In
    // particular, an integral model with a nonzero objective may still be
    // infeasible and carry a complete Farkas/tree/PB refutation.  Pre-refusing
    // that model shape would discard a proof before learning which claim the
    // solve actually needs to make.

    let mut opts = SolveOpts::new().with_time_limit(Duration::from_secs_f64(secs));
    if require == Require::Full {
        opts = opts.with_require_certificates(true);
    }
    let tree_cert_leaves_explicit =
        flag_or_env(&flags, "tree-cert-leaves", "AY_MILP_TREE_CERT_LEAVES");
    if let Some(v) = &tree_cert_leaves_explicit {
        match v.parse::<usize>() {
            Ok(n) => opts = opts.with_tree_cert_leaves(n),
            Err(_) => return die("--tree-cert-leaves needs an integer"),
        }
    }
    // A TREE CERTIFICATE WITH NO CONSUMER IS NOT BOUGHT.
    //
    // The artifact is paid for by a whole re-solve (`harvest_tree_cert_by_resolve`),
    // and `--no-emit-cert` used to leave the leaf budget at its 256 default — so the
    // re-solve ran on every infeasible verdict and the result was thrown away
    // unwritten. Measured over 8 infeasible bench instances: 8.638 s -> 7.539 s
    // (-1.099 s, 12.7%), worst case neos859080 1.131 -> 0.386 s (2.93x), at
    // byte-identical verdicts.
    //
    // `--require full` is EXCLUDED because that posture must be able to refuse a
    // verdict it cannot back: the evidence has to exist even when it is not written.
    // An explicit `--tree-cert-leaves`/`AY_MILP_TREE_CERT_LEAVES` is also honoured —
    // asking for a budget outright is a deliberate act, and silently zeroing it would
    // make the knob lie.
    //
    // This is what makes a larger evidence-path budget affordable at all: the cost of
    // proving is now charged only to callers who asked to be able to check.
    if flags.has("no-emit-cert") && require != Require::Full && tree_cert_leaves_explicit.is_none()
    {
        opts = opts.with_tree_cert_leaves(0);
    }
    if let Some(v) = flag_or_env(&flags, "threads", "AY_MILP_THREADS") {
        match v.parse::<u32>() {
            Ok(n) if n > 1 => opts = opts.with_threads(n).with_determinism(false),
            Ok(_) => {}
            Err(_) => return die("--threads needs an integer"),
        }
    }
    if let Some(v) = flags.get("seed") {
        match v.parse::<u64>() {
            Ok(n) => opts = opts.with_seed(n),
            Err(_) => return die("--seed needs an integer"),
        }
    }
    if flags.has("deterministic") {
        opts = opts.with_determinism(true);
    }
    if flags.has("no-deterministic") {
        opts = opts.with_determinism(false);
    }
    if let Some(v) = flag_or_env(&flags, "memory-budget", "AY_MILP_OPEN_BYTES") {
        match v.parse::<usize>() {
            Ok(n) => opts = opts.with_memory_budget(Some(n)),
            Err(_) => return die("--memory-budget needs an integer"),
        }
    }

    let col_names = p.col_names.clone();
    let obj_scale = p.obj_scale.clone();
    let mut s = match BabSession::new(p.model, &opts) {
        Ok(s) => s,
        Err(e) => {
            println!("SETUP_ERROR {e:?} - -");
            return ExitCode::from(4);
        }
    };
    if let Some(seedf) = flag_or_env(&flags, "seed-solution", "AY_MILP_SEED_SOL") {
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
    if let Some(cp) = &cert_path {
        let t = Instant::now();
        let ctx = cert_io::EmitCtx {
            model: s.model(),
            model_text: &text,
            col_names: &col_names,
            obj_scale: &obj_scale,
            provenance: &provenance(),
            replay_claims: s.replay_claims(),
            parity_infeasibility_certificate: s.parity_infeasibility_certificate(),
            sat_relu_infeasibility_certificate: s.sat_relu_infeasibility_certificate(),
            network_design_infeasibility_certificate: s.network_design_infeasibility_certificate(),
            network_design_optimality_certificate: s.network_design_optimality_certificate(),
            block_angular_optimality_certificate: s.block_angular_optimality_certificate(),
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
                "certificate: {cp} ({bytes} bytes, {} us)",
                t.elapsed().as_micros()
            ),
            Err(e) => eprintln!("ay-milp: WARNING: cannot write {cp}: {e}"),
        }
    }

    // --emit-witness works on EVERY verdict that has a point, which is the whole
    // point: `AY_DUMP_SOL` only ever fired on `Feasible`.
    let witness_path = flag_or_env(&flags, "emit-witness", "AY_DUMP_SOL");
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
    // `finish` gate already re-validates every verdict's witness; this makes
    // the guarantee CONTRACTUAL by re-checking here, independently, and failing
    // the run rather than printing an unbacked verdict.
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
fn solve_json_line(
    status: &str,
    value: Option<&str>,
    dual_bound: Option<&str>,
    detail: Option<&str>,
    dt: f64,
    nodes: u64,
    replay_claims: usize,
) -> String {
    format!(
        "{{\"status\":\"{}\",\"value\":{},\"dual_bound\":{},\"detail\":{},\"time\":{dt:.3},\"nodes\":{nodes},\"replay_claims\":{replay_claims}}}",
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
    let flags = match Flags::parse(args, &["model", "cert"]) {
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
    for n in &report.notes {
        println!("  {n}");
    }
    for c in &report.claims {
        println!(
            "  claim {:<11} {:<9} {}  {}",
            c.name,
            c.kind.token(),
            if c.verified { "ok    " } else { "NOT-OK" },
            c.detail
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
        .claims
        .iter()
        .any(|c| c.kind == cert_io::EvidenceKind::Replay);

    // The word VERIFIED is reserved. `--accept-replay` prints
    // ACCEPTED-ON-TRUST and still exits non-zero unless `--exit-zero` is ALSO
    // passed. Deliberately two flags: a wrapper doing `ay-milp verify && echo
    // ok` must not be able to conflate trust with proof by accident.
    //
    // `Partial` is accepted here for the same reason `Unverified` is: it is the
    // same aggregate ("nothing refuted; something has no object"), only more
    // precisely reported. It still cannot reach exit 0 without BOTH flags.
    if matches!(
        report.status,
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
        return ExitCode::from(report.status.exit_code() as u8);
    }
    println!("{}", report.status.word());
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    ExitCode::from(report.status.exit_code() as u8)
}

// ---------------------------------------------------------------------------
// check-point — the standalone primal checker, promoted to a command
// ---------------------------------------------------------------------------

fn cmd_check_point(args: &[String]) -> ExitCode {
    let flags = match Flags::parse(
        args,
        &["model", "point", "repair-time-limit", "memory-budget"],
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
    let idx = name_index(&p.col_names);
    let mut x = vec![BigRational::zero(); p.model.num_cols()];
    let mut supplied = vec![None; p.model.num_cols()];
    let mut hits = 0usize;
    for line in point_text.lines() {
        let l = line.trim();
        if l.is_empty() || l.starts_with('#') {
            continue;
        }
        let f: Vec<&str> = l.split_whitespace().collect();
        // Accept the three shapes: `name value`, `x <j> <name> <value>`, and a
        // bare `<value>` column list is deliberately NOT accepted (too easy to
        // misalign silently).
        let (key, val) = match f[..] {
            [n, v] => (n, v),
            ["x", _, n, v] => (n, v),
            _ => continue,
        };
        // Parsed from the DECIMAL TEXT as an exact rational, not through f64:
        // `0.9` is nine tenths, and an exact checker that read the nearest
        // double would adjudicate a model nobody wrote.
        let Some(v) = parse_decimal_exact(val) else {
            continue;
        };
        if let Some(&j) = idx.get(key) {
            x[j] = v.clone();
            supplied[j] = Some(v);
            hits += 1;
        }
    }
    println!("point: {hits} of {} columns named", p.model.num_cols());
    match p.model.check_point(&x) {
        Ok(()) => {
            let v = p.model.objective_value_at(&x);
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
            let repair_time_limit = match flags
                .get("repair-time-limit")
                .map_or(Ok(10.0), |value| value.parse::<f64>())
            {
                Ok(value) if value.is_finite() && value > 0.0 => value,
                _ => return die("--repair-time-limit needs a positive finite number"),
            };
            let memory_budget = match flags.get("memory-budget") {
                Some(value) => match value.parse::<usize>() {
                    Ok(value) => Some(value),
                    Err(_) => return die("--memory-budget needs an integer"),
                },
                None => None,
            };
            println!(
                "point: decimal text failed exact checking ({v:?}); attempting continuous repair"
            );
            match repair_continuous_completion(
                &p.model,
                &supplied,
                Duration::from_secs_f64(repair_time_limit),
                memory_budget,
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
mod point_repair_tests {
    use super::*;
    use ay_milp::{Model, Sense};

    fn thirds_model() -> Model {
        let mut model = Model::new();
        let integer = model.add_int_col(0.0, 1.0);
        let continuous = model.add_col(0.0, 1.0);
        model.add_row(0.0, 0.0, &[(integer, -1.0), (continuous, 3.0)]);
        model.set_objective(&[(continuous, 1.0)], Sense::Minimize);
        model
    }

    #[test]
    fn rounded_continuous_value_is_repaired_with_integer_assignment_fixed() {
        let model = thirds_model();
        let supplied = vec![
            Some(BigRational::one()),
            Some(BigRational::new(
                BigInt::from(333_333_333_333_333_i64),
                BigInt::from(1_000_000_000_000_000_i64),
            )),
        ];
        assert!(model
            .check_point(
                &supplied
                    .iter()
                    .map(|value| value.clone().expect("complete point"))
                    .collect::<Vec<_>>()
            )
            .is_err());

        let repaired =
            repair_continuous_completion(&model, &supplied, Duration::from_secs(2), Some(64 << 20))
                .expect("the exact LP completion exists");
        assert_eq!(repaired[0], BigRational::one());
        assert_eq!(
            repaired[1],
            BigRational::new(BigInt::from(1), BigInt::from(3))
        );
        assert!(model.check_point(&repaired).is_ok());
    }

    #[test]
    fn repair_refuses_missing_or_fractional_integral_assignments() {
        let model = thirds_model();
        let missing = vec![None, Some(BigRational::zero())];
        assert!(repair_continuous_completion(
            &model,
            &missing,
            Duration::from_secs(2),
            Some(64 << 20),
        )
        .is_err());

        let fractional = vec![
            Some(BigRational::new(BigInt::from(1), BigInt::from(2))),
            Some(BigRational::zero()),
        ];
        assert!(repair_continuous_completion(
            &model,
            &fractional,
            Duration::from_secs(2),
            Some(64 << 20),
        )
        .is_err());
    }

    #[test]
    fn pure_lp_decimal_point_can_be_reconstructed_exactly() {
        let mut model = Model::new();
        let continuous = model.add_col(0.0, 1.0);
        model.add_row(1.0, 1.0, &[(continuous, 3.0)]);
        model.set_objective(&[(continuous, 1.0)], Sense::Minimize);
        let supplied = vec![Some(BigRational::new(
            BigInt::from(333_333_333_333_333_i64),
            BigInt::from(1_000_000_000_000_000_i64),
        ))];
        let repaired =
            repair_continuous_completion(&model, &supplied, Duration::from_secs(2), Some(64 << 20))
                .expect("the exact LP vertex exists");
        assert_eq!(
            repaired,
            vec![BigRational::new(BigInt::from(1), BigInt::from(3))]
        );
    }

    #[test]
    fn repair_rejects_an_integer_the_numeric_model_cannot_represent() {
        let mut model = Model::new();
        model.add_int_col(f64::NEG_INFINITY, f64::INFINITY);
        let supplied = vec![Some(BigRational::from_integer(BigInt::from(
            9_007_199_254_740_993_u64,
        )))];
        let error =
            repair_continuous_completion(&model, &supplied, Duration::from_secs(2), Some(64 << 20))
                .expect_err("2^53 + 1 is not exactly representable as f64");
        assert!(error.contains("cannot be represented exactly"), "{error}");
    }
}

// ---------------------------------------------------------------------------
// diag — the old env-var modes, as subcommands
// ---------------------------------------------------------------------------

fn cmd_diag(args: &[String]) -> ExitCode {
    let flags = match Flags::parse(args, &["time-limit", "memory-budget", "row", "solution"]) {
        Ok(f) => f,
        Err(e) => return die(&e),
    };
    let Some(mode) = flags.positional.first().cloned() else {
        return die("diag needs a mode \
             (root-closure|lp-only|dualfix|block-angular|margin-row|cross-check|profile)");
    };
    let Some(path) = flags.positional.get(1).cloned() else {
        return die("diag needs a model file");
    };
    let secs: f64 = flags
        .get("time-limit")
        .and_then(|s| s.parse().ok())
        .or_else(|| flags.positional.get(2).and_then(|s| s.parse().ok()))
        .unwrap_or(60.0);
    let text = match read_maybe_gz(&path) {
        Ok(t) => t,
        Err(e) => return die(&format!("cannot read {path}: {e}")),
    };
    let p = match ay_milp::read_mps(&text) {
        Ok(p) => p,
        Err(e) => return die(&format!("PARSE_ERROR {e}")),
    };
    report_shape(&p);
    match mode.as_str() {
        "root-closure" => {
            let line = ay_milp::diag_root_closure(&p.model, secs);
            // The diagnostic reports in the model's sense/offset frame; what it
            // cannot undo is the reader's integralising objective scale.
            let scale = p.obj_scale.to_f64().unwrap_or(1.0);
            let rescaled = line
                .split_whitespace()
                .map(|tok| match tok.split_once('=') {
                    Some((k @ ("bound_lp" | "bound_cut" | "gain"), v)) => {
                        let x: f64 = v.parse().unwrap_or(f64::NAN);
                        format!("{k}={}", x / scale)
                    }
                    _ => tok.to_string(),
                })
                .collect::<Vec<_>>()
                .join(" ");
            println!("{rescaled}");
            ExitCode::SUCCESS
        }
        "lp-only" => {
            eprintln!("{}", ay_milp::diag_float_lp(&p.model, secs));
            print_profiles();
            ExitCode::SUCCESS
        }
        // What DUAL FIXING does to this model, without solving it. `int_prop_only`
        // is the `DualReductions=0` arm and `int_after` the default one, both
        // measured on the same pass so the attribution needs no second run.
        "dualfix" => {
            println!("{}", ay_milp::diag_dualfix(&p.model, secs));
            ExitCode::SUCCESS
        }
        "block-angular" => {
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
        "margin-row" => {
            let spec = flags
                .get("row")
                .cloned()
                .or_else(|| std::env::var("AY_MILP_MARGIN_ROW").ok())
                .unwrap_or_else(|| "last".into());
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
            eprintln!("{}", ay_milp::diag_margin_reframe(&m, secs));
            ExitCode::SUCCESS
        }
        "cross-check" => {
            let Some(sol) = flags
                .get("solution")
                .cloned()
                .or_else(|| std::env::var("AY_CHECK_SOL").ok())
            else {
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
            let opts = SolveOpts::new().with_time_limit(Duration::from_secs_f64(secs));
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
        "profile" => {
            let opts = SolveOpts::new().with_time_limit(Duration::from_secs_f64(secs));
            let mut s = match BabSession::new(p.model, &opts) {
                Ok(s) => s,
                Err(e) => return die(&format!("{e:?}")),
            };
            let t0 = Instant::now();
            let o = s.check();
            eprintln!(
                "profile: {:?} in {:.3}s",
                o.map(|x| x.is_sat()),
                t0.elapsed().as_secs_f64()
            );
            print_profiles();
            ExitCode::SUCCESS
        }
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
    let flags = match Flags::parse(args, &["bucket"]) {
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
    let flags = match Flags::parse(args, &[]) {
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
    if !path.ends_with(".gz") {
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
mod json_output_tests {
    use super::*;
    use ay_milp::{Model, UnknownReason};

    /// The `--format json` line for an outcome, built exactly as `cmd_solve`
    /// builds it: `verdict_line` then `solve_json_line`. Only the numbers are
    /// stand-ins.
    fn emit(o: &Outcome) -> String {
        let mut m = Model::new();
        m.add_col(0.0, 1.0);
        let scale = BigRational::one();
        let (status, value, detail) = verdict_line(o, &m, &scale, 1.5, 7);
        solve_json_line(
            &status,
            value.as_deref(),
            None,
            detail.as_deref(),
            1.5,
            7,
            0,
        )
    }

    fn parse(line: &str) -> serde_json::Value {
        serde_json::from_str(line)
            .unwrap_or_else(|e| panic!("`--format json` emitted invalid JSON: {e}\n  {line}"))
    }

    fn point() -> Vec<BigRational> {
        vec![BigRational::zero()]
    }

    /// EVERY `UnknownReason` in `outcome.rs`, in declaration order. `Outcome`
    /// and `UnknownReason` are `#[non_exhaustive]`, so this crate cannot get a
    /// compile-time exhaustiveness check on them — `outcome.rs`'s
    /// `cli_json_coverage` test carries that check (it lives in the defining
    /// crate, where the match IS exhaustive) and names this list.
    fn every_unknown_reason() -> Vec<UnknownReason> {
        vec![
            UnknownReason::Timeout,
            UnknownReason::Interrupted,
            UnknownReason::IterationLimit,
            UnknownReason::MemoryLimit,
            UnknownReason::CertificateUnavailable,
            UnknownReason::SolverIncomplete {
                detail: "branch-and-bound could not settle every node".to_owned(),
            },
            UnknownReason::WitnessRejected {
                detail: "the verdict's point is infeasible".to_owned(),
            },
        ]
    }

    /// EVERY `Outcome` in `outcome.rs`, in declaration order, paired with the
    /// status token the CLI must print for it.
    fn every_outcome() -> Vec<(&'static str, Outcome)> {
        let mut v = vec![
            (
                "OPTIMAL",
                Outcome::Optimal {
                    value: BigRational::zero(),
                    model_values: point(),
                    cert: None,
                },
            ),
            (
                "FEASIBLE",
                Outcome::Feasible {
                    model_values: point(),
                    incumbent_only: true,
                    dual_bound: None,
                },
            ),
            (
                "INFEASIBLE",
                Outcome::Infeasible {
                    cert: None,
                    tree_cert: None,
                },
            ),
            ("UNBOUNDED", Outcome::Unbounded),
            (
                "BOUND",
                Outcome::Bound {
                    dual_bound: BigRational::zero(),
                    rigorous: true,
                },
            ),
        ];
        v.extend(
            every_unknown_reason()
                .into_iter()
                .map(|reason| ("UNKNOWN", Outcome::Unknown { reason })),
        );
        v
    }

    /// THE REGRESSION. Before the fix, `verdict_line` returned
    /// `UNKNOWN SolverIncomplete { detail: "branch-and-bound could not settle
    /// every node" }` as the whole status and it was interpolated raw into the
    /// `"status"` literal, so the inner quotes terminated the string and a real
    /// parser stopped at the `S` of `SolverIncomplete`.
    #[test]
    fn a_debug_payload_status_is_still_json() {
        let line = emit(&Outcome::Unknown {
            reason: UnknownReason::SolverIncomplete {
                detail: "branch-and-bound could not settle every node".to_owned(),
            },
        });
        let v = parse(&line);
        assert_eq!(v["status"], "UNKNOWN");
        assert_eq!(
            v["detail"],
            "SolverIncomplete { detail: \"branch-and-bound could not settle every node\" }",
            "the payload must survive the round trip, not just parse"
        );
    }

    /// Not just the observed one: every status the CLI can print. (`OTHER` is
    /// covered separately — a future `#[non_exhaustive]` variant cannot be
    /// constructed here to reach the arm that produces it.)
    #[test]
    fn every_status_emits_valid_json() {
        for (want, o) in every_outcome() {
            let line = emit(&o);
            let v = parse(&line);
            assert_eq!(v["status"], want, "wrong status token for {o:?}\n  {line}");
            // The status is the discriminator, so it must stay a bare token —
            // a `Debug` blob smuggled back in would parse but be unmatchable.
            assert!(
                v["status"]
                    .as_str()
                    .is_some_and(|s| s.chars().all(|c| c.is_ascii_uppercase() || c == '-')),
                "status must be an enumerable token, got {:?}",
                v["status"]
            );
            assert!(v["time"].is_number() && v["nodes"].is_number());
        }
    }

    /// The `OTHER` arm carries a whole `Outcome`'s `Debug`, not a reason's, and
    /// `#[non_exhaustive]` means no variant reaching it can be constructed from
    /// this crate. Drive the emission path with exactly the string that arm
    /// builds so the catch-all is not the one shape nobody ever parsed.
    #[test]
    fn the_non_exhaustive_catch_all_emits_valid_json() {
        let blob = format!(
            "{:?}",
            Outcome::Unknown {
                reason: UnknownReason::SolverIncomplete {
                    detail: "a \"quoted\" payload".to_owned(),
                },
            }
        );
        let line = solve_json_line("OTHER", None, None, Some(&blob), 1.5, 7, 0);
        let v = parse(&line);
        assert_eq!(v["status"], "OTHER");
        assert_eq!(v["detail"], blob);
    }

    /// ⚠ A partial escape is the same bug with a smaller trigger. The quote is
    /// what broke today; a backslash, a newline, a tab or a bare control
    /// character each break a quote-only escaper. `Debug` renders some of these
    /// itself, so drive the escaper directly as well as through an outcome.
    #[test]
    fn escaping_covers_more_than_the_double_quote() {
        let nasty = "quote \" backslash \\ newline \n cr \r tab \t bs \u{8} ff \u{c} nul \u{0} \
                     unit-sep \u{1f} unicode ü▲";
        let line = emit(&Outcome::Unknown {
            reason: UnknownReason::WitnessRejected {
                detail: nasty.to_owned(),
            },
        });
        let v = parse(&line);
        assert_eq!(v["status"], "UNKNOWN");
        assert_eq!(
            v["detail"],
            format!(
                "{:?}",
                UnknownReason::WitnessRejected {
                    detail: nasty.to_owned()
                }
            ),
            "the escaped detail must decode back to the exact Debug string"
        );

        // And the escaper on its own, against a real parser's idea of a string.
        let escaped = json_escape(nasty);
        let round: serde_json::Value = serde_json::from_str(&format!("\"{escaped}\""))
            .unwrap_or_else(|e| panic!("json_escape produced an unparseable literal: {e}"));
        assert_eq!(round, nasty);
        assert!(
            !escaped.contains('\n') && !escaped.contains('\t'),
            "raw control characters are not legal inside a JSON string: {escaped:?}"
        );
    }

    /// The line (non-JSON) shape is frozen — the journal's measurement scripts
    /// read it — so splitting status/detail must re-join byte for byte.
    #[test]
    fn the_line_format_is_unchanged_by_the_split() {
        let mut m = Model::new();
        m.add_col(0.0, 1.0);
        let scale = BigRational::one();
        let o = Outcome::Unknown {
            reason: UnknownReason::SolverIncomplete {
                detail: "branch-and-bound could not settle every node".to_owned(),
            },
        };
        let (status, value, detail) = verdict_line(&o, &m, &scale, 1.5, 7);
        let rejoined = format!(
            "{status}{} {}",
            detail.map_or(String::new(), |d| format!(" {d}")),
            value.as_deref().unwrap_or("-")
        );
        assert_eq!(
            rejoined,
            "UNKNOWN SolverIncomplete { detail: \"branch-and-bound could not settle every node\" } -"
        );
    }
}
