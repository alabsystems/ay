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
use ay_milp::{BabSession, ColKind, MpsProblem, Outcome, SolveOpts};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

const USAGE: &str = "\
ay-milp — MILP/LP engine with certified verdicts

USAGE
  ay-milp solve <file.mps[.gz]> [options]
  ay-milp verify --model <file.mps> --cert <file.ayc> [--accept-replay] [--exit-zero]
  ay-milp check-point --model <file.mps> --point <file.sol>
  ay-milp diag <root-closure|lp-only|margin-row|cross-check|profile> <file.mps> [options]
  ay-milp knobs [--list] [--bucket <b>] [--audit] [--deprecated]
  ay-milp features --list
  ay-milp replay-claims

solve options
  --time-limit <secs>          wall-clock limit (default 60)
  --threads <n>                worker threads (>1 opts out of determinism)
  --seed <n>                   RNG seed
  --deterministic|--no-deterministic
  --memory-budget <bytes>      open-node retention budget
  --tree-cert-leaves <n>       tree-certificate leaf budget (default 256; 0 = off)
  --seed-solution <path>       reference incumbent, `name value` per line (advice only)
  --require <none|witness|full>   evidence posture (DEFAULT: witness)
  --emit-cert <path.ayc>       certificate path (DEFAULT: <input>.ayc)
  --no-emit-cert               opt out of certificate emission
  --emit-cert-max-bytes <n>    cap; an overflowing block is DROPPED and its claim downgraded
  --emit-witness <path>        write the witness on ANY verdict that has one
  --witness-format <ay|sol|rational>   default: rational
  --format <line|json>         stdout shape (default line)

verify exits:  0 VERIFIED   10 UNVERIFIED   20 REFUTED   30 MISMATCH
The word VERIFIED is reserved: a REPLAY claim never earns exit 0.
";

fn main() -> ExitCode {
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

    // `--require full` MUST REFUSE, not silently return Unknown.
    //
    // Measured: on markshare1 / cd_m7_s1 / misc07 / pk1, `require_certificates:
    // true` turns 4 of 4 OPTIMAL verdicts into `Unknown(CertificateUnavailable)`
    // — markshare1's OPTIMAL 1, this project's flagship result, included. The
    // cause is structural, not a budget miss: an `OptimalityCertificate` is an
    // LP-duality object and cannot express "no INTEGER point beats v" when the
    // LP bound is weaker than v, and there is no optimality analogue of the
    // infeasibility lane's tree capture anywhere in the crate. Someone who turns
    // this on without being told would watch the corpus collapse and file a
    // regression, so it refuses with the reason instead.
    if require == Require::Full && p.model.has_integrality() && p.model.has_objective() {
        let nonzero_obj = (0..p.model.num_cols())
            .filter_map(|j| p.model.col_at(j))
            .any(|c| p.model.obj_coeff(c) != 0.0);
        if nonzero_obj {
            eprintln!(
                "ay-milp: --require full REFUSED: no MILP optimality certificate exists in this \
                 build. An OptimalityCertificate is an LP-duality object; it cannot express \"no \
                 integer point beats v\" when the LP bound is weaker than v. Use `--require \
                 witness` (the default) — the primal half IS succinctly checkable and this build \
                 emits it."
            );
            return ExitCode::from(2);
        }
    }

    let mut opts = SolveOpts::new().with_time_limit(Duration::from_secs_f64(secs));
    if require == Require::Full {
        opts = opts.with_require_certificates(true);
    }
    if let Some(v) = flag_or_env(&flags, "tree-cert-leaves", "AY_MILP_TREE_CERT_LEAVES") {
        match v.parse::<usize>() {
            Ok(n) => opts = opts.with_tree_cert_leaves(n),
            Err(_) => return die("--tree-cert-leaves needs an integer"),
        }
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
    let line = verdict_line(&outcome, s.model(), &obj_scale, dt, nodes);
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
            "{{\"status\":\"{}\",\"value\":{},\"dual_bound\":{},\"time\":{dt:.3},\"nodes\":{nodes},\"replay_claims\":{}}}",
            line.0,
            line.1.as_deref().unwrap_or("null"),
            bound.as_deref().unwrap_or("null"),
            s.replay_claims().len()
        );
    } else {
        println!(
            "{} {} {dt:.3} {nodes}{}",
            line.0,
            line.1.as_deref().unwrap_or("-"),
            bound.map_or(String::new(), |b| format!(" bound={b}"))
        );
    }
    for rc in s.replay_claims() {
        eprintln!(
            "replay claim: {} — NOT certified. Re-verification means re-running the solver; tcb {}",
            rc.claim, rc.tcb
        );
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

fn verdict_line(
    o: &Outcome,
    model: &ay_milp::Model,
    obj_scale: &BigRational,
    _dt: f64,
    _nodes: u64,
) -> (String, Option<String>) {
    match o {
        Outcome::Optimal { value, .. } => ("OPTIMAL".into(), Some(decimal(&(value / obj_scale)))),
        Outcome::Feasible { model_values, .. } => {
            let v = model.objective_value_at(model_values);
            ("FEASIBLE".into(), Some(decimal(&(&v / obj_scale))))
        }
        Outcome::Infeasible { .. } => ("INFEASIBLE".into(), None),
        Outcome::Unbounded => ("UNBOUNDED".into(), None),
        Outcome::Bound { dual_bound, .. } => {
            ("BOUND".into(), Some(decimal(&(dual_bound / obj_scale))))
        }
        Outcome::Unknown { reason } => (format!("UNKNOWN {reason:?}"), None),
        other => (format!("OTHER {other:?}"), None),
    }
}

fn write_witness(
    path: &str,
    x: &[BigRational],
    names: &[String],
    fmt: &str,
) -> std::io::Result<()> {
    let mut f = std::fs::File::create(path)?;
    if fmt == "ay" {
        writeln!(f, "# ay-milp witness, {} columns, exact rationals", x.len())?;
    }
    for (j, v) in x.iter().enumerate() {
        let name = names.get(j).map_or("-", String::as_str);
        match fmt {
            // Historical `AY_DUMP_SOL` shape: what every other solver prints.
            // Lossy on purpose — a comparison script reads it, not a checker.
            "sol" => writeln!(f, "{name} {}", decimal(v))?,
            "ay" => writeln!(f, "x {j} {name} {}", rat(v))?,
            _ => writeln!(f, "{name} {}", rat(v))?,
        }
    }
    Ok(())
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
    let replay = report
        .claims
        .iter()
        .any(|c| c.kind == cert_io::EvidenceKind::Replay);

    // The word VERIFIED is reserved. `--accept-replay` prints
    // ACCEPTED-ON-TRUST and still exits non-zero unless `--exit-zero` is ALSO
    // passed. Deliberately two flags: a wrapper doing `ay-milp verify && echo
    // ok` must not be able to conflate trust with proof by accident.
    if report.status == cert_io::CheckStatus::Unverified && replay && flags.has("accept-replay") {
        println!("ACCEPTED-ON-TRUST (replay claims were NOT verified)");
        if flags.has("exit-zero") {
            return ExitCode::SUCCESS;
        }
        return ExitCode::from(10);
    }
    println!("{}", report.status.word());
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    ExitCode::from(report.status.exit_code() as u8)
}

// ---------------------------------------------------------------------------
// check-point — the standalone primal checker, promoted to a command
// ---------------------------------------------------------------------------

fn cmd_check_point(args: &[String]) -> ExitCode {
    let flags = match Flags::parse(args, &["model", "point"]) {
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
            x[j] = v;
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
        Err(v) => {
            println!("INFEASIBLE  {v:?}");
            ExitCode::from(20)
        }
    }
}

// ---------------------------------------------------------------------------
// diag — the old env-var modes, as subcommands
// ---------------------------------------------------------------------------

fn cmd_diag(args: &[String]) -> ExitCode {
    let flags = match Flags::parse(args, &["time-limit", "row", "solution"]) {
        Ok(f) => f,
        Err(e) => return die(&e),
    };
    let Some(mode) = flags.positional.first().cloned() else {
        return die("diag needs a mode (root-closure|lp-only|margin-row|cross-check|profile)");
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
