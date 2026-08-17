// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use ay_pb::dev_tools::{
    self, ProbeConfig, ProbeEngine, TwoClubBranchRule, TwoClubConfig, TwoClubOutcome,
    TwoClubPartition, TwoClubSdpConfig,
};
use ay_pb::veripb_runner::{verify_unsat, VeriPbEnvelope};
use sha2::{Digest, Sha256};

// Developer campaigns use the same live-allocation signal as the production
// ay-pb binary. The outer OOM guard still accounts for the complete process
// group, including certificate workers.
#[global_allocator]
static GLOBAL: ay_sys::CountingAllocator<std::alloc::System> =
    ay_sys::CountingAllocator::new(std::alloc::System);

const USAGE: &str = "\
ay-pb-dev: explicit, bounded developer campaigns

USAGE:
  ay-pb-dev two-club INSTANCE [--seed FILE] [--seconds N] [--max-nodes N]
      [--worker W --workers N [--pivot-k K | --d2-base N --d2-classes C,...]]
      [--branch first|viol|marked|marked-min] [--trace] [--dump-frontier] [--no-lp]
      [--lp-warmup N] [--lp-cadence N] [--lp-window N] [--lp-max-rows N]
      [--lp-low-margin N] [--lp-exact-margin N] [--no-lp-ceiling]
      [--nbhd-rows] [--sdp-worker FILE]
  ay-pb-dev probe bnn|bnb|sls|lp|safe-lp|milp|floor INSTANCE
      [--seconds N] [--node-budget N]
  ay-pb-dev certify-unsat FILE... [--limit N] --veripb FILE [--proof-dir DIR]
  ay-pb-dev certify-koops ROOT --limit N [--match TEXT]
      --veripb FILE [--proof-dir DIR]
  ay-pb-dev certify-mat98 FILE --veripb FILE [--proof-dir DIR]
  ay-pb-dev farkas-anchor OUTPUT_DIR
  ay-pb-dev export-wbo INPUT.wbo OUTPUT.opb
  ay-pb-dev export-nlc INPUT.opb OUTPUT.opb

`certify-koops --match mat98` is the bounded real mat98 campaign. Every
certify-* command requires external VeriPB verification before reporting a
VERIFIED result.
";

#[derive(Default)]
struct ParsedArgs {
    positional: Vec<String>,
    values: BTreeMap<String, String>,
    flags: BTreeSet<String>,
}

fn parse_args(
    args: impl IntoIterator<Item = String>,
    value_options: &[&str],
    flag_options: &[&str],
) -> Result<ParsedArgs, String> {
    let value_options: BTreeSet<&str> = value_options.iter().copied().collect();
    let flag_options: BTreeSet<&str> = flag_options.iter().copied().collect();
    let mut parsed = ParsedArgs::default();
    let mut args = args.into_iter();
    while let Some(argument) = args.next() {
        if value_options.contains(argument.as_str()) {
            let value = args
                .next()
                .ok_or_else(|| format!("{argument} requires a value"))?;
            if parsed.values.insert(argument.clone(), value).is_some() {
                return Err(format!("{argument} may be specified only once"));
            }
        } else if flag_options.contains(argument.as_str()) {
            if !parsed.flags.insert(argument.clone()) {
                return Err(format!("{argument} may be specified only once"));
            }
        } else if argument.starts_with('-') {
            return Err(format!("unknown option {argument}"));
        } else {
            parsed.positional.push(argument);
        }
    }
    Ok(parsed)
}

fn value<'a>(args: &'a ParsedArgs, name: &str) -> Option<&'a str> {
    args.values.get(name).map(String::as_str)
}

fn parse_number<T>(args: &ParsedArgs, name: &str, default: T) -> Result<T, String>
where
    T: std::str::FromStr,
{
    match value(args, name) {
        Some(raw) => raw
            .parse()
            .map_err(|_| format!("{name} expects a non-negative integer, got {raw:?}")),
        None => Ok(default),
    }
}

fn required_number<T>(args: &ParsedArgs, name: &str) -> Result<T, String>
where
    T: std::str::FromStr,
{
    let raw = value(args, name).ok_or_else(|| format!("{name} is required"))?;
    raw.parse()
        .map_err(|_| format!("{name} expects a non-negative integer, got {raw:?}"))
}

fn parse_two_club_branch(raw: Option<&str>) -> Result<TwoClubBranchRule, String> {
    match raw.unwrap_or("first") {
        "first" => Ok(TwoClubBranchRule::First),
        "viol" => Ok(TwoClubBranchRule::ViolatingDegree),
        "marked" => Ok(TwoClubBranchRule::Marked),
        "marked-min" => Ok(TwoClubBranchRule::MarkedMinDegree),
        other => Err(format!(
            "--branch must be first, viol, marked, or marked-min, got {other:?}"
        )),
    }
}

fn read_opb(path: &Path) -> Result<ay_pb::PbInstance, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|error| format!("read {}: {error}", path.display()))?;
    ay_pb::parse_opb(&text).map_err(|error| format!("parse {}: {error}", path.display()))
}

fn read_seed(path: &Path, variables: usize) -> Result<Vec<bool>, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|error| format!("read {}: {error}", path.display()))?;
    let seed: Vec<bool> = text
        .split_whitespace()
        .map(|token| match token {
            "0" => Ok(false),
            "1" => Ok(true),
            _ => Err(format!(
                "{} contains seed token {token:?}; expected only 0 or 1",
                path.display()
            )),
        })
        .collect::<Result<_, _>>()?;
    if seed.len() != variables {
        return Err(format!(
            "{} has {} seed values; instance has {variables} variables",
            path.display(),
            seed.len()
        ));
    }
    Ok(seed)
}

fn apply_memory_limit() {
    let bytes = std::env::var("MEMLIMIT")
        .ok()
        .and_then(|value| value.trim().parse::<usize>().ok())
        .filter(|&mib| mib > 0)
        .map_or_else(ay_sys::default_memory_limit, |mib| {
            let hard_limit = mib.saturating_mul(1024 * 1024);
            hard_limit - hard_limit / 10
        });
    if bytes > 0 {
        ay_sys::set_process_memory_limit(bytes);
    }
}

fn two_club(args: Vec<String>) -> Result<(), String> {
    let args = parse_args(
        args,
        &[
            "--seed",
            "--seconds",
            "--max-nodes",
            "--worker",
            "--workers",
            "--pivot-k",
            "--d2-base",
            "--d2-classes",
            "--branch",
            "--lp-warmup",
            "--lp-cadence",
            "--lp-window",
            "--lp-max-rows",
            "--lp-low-margin",
            "--lp-exact-margin",
            "--sdp-worker",
        ],
        &[
            "--trace",
            "--dump-frontier",
            "--no-lp",
            "--no-lp-ceiling",
            "--nbhd-rows",
        ],
    )?;
    let [instance_path] = args.positional.as_slice() else {
        return Err("two-club requires exactly one INSTANCE".to_owned());
    };
    let instance_path = Path::new(instance_path);
    let instance = read_opb(instance_path)?;
    let objective = instance
        .objective
        .as_ref()
        .ok_or_else(|| format!("{} has no objective", instance_path.display()))?;
    let seed = value(&args, "--seed")
        .map(|path| read_seed(Path::new(path), instance.num_vars as usize))
        .transpose()?;
    if let Some(seed) = &seed {
        eprintln!(
            "seed loaded: {} vars, {} selected",
            seed.len(),
            seed.iter().filter(|&&selected| selected).count()
        );
    }

    let seconds: u64 = parse_number(&args, "--seconds", 300)?;
    if seconds == 0 {
        return Err("--seconds must be positive".to_owned());
    }
    let worker = value(&args, "--worker")
        .map(|_| required_number::<usize>(&args, "--worker"))
        .transpose()?;
    let workers = value(&args, "--workers")
        .map(|_| required_number::<usize>(&args, "--workers"))
        .transpose()?;
    if worker.is_some() != workers.is_some() {
        return Err("--worker and --workers must be supplied together".to_owned());
    }
    let partition = match (
        value(&args, "--pivot-k"),
        value(&args, "--d2-base"),
        value(&args, "--d2-classes"),
        worker,
        workers,
    ) {
        (Some(_), Some(_), _, _, _) | (Some(_), _, Some(_), _, _) => {
            return Err("--pivot-k cannot be combined with depth-two options".to_owned());
        }
        (Some(_), None, None, Some(worker), Some(workers)) => TwoClubPartition::Pivot {
            pivot_count: required_number(&args, "--pivot-k")?,
            worker,
            workers,
        },
        (None, Some(_), Some(classes), Some(worker), Some(workers)) => {
            let classes = classes
                .split(',')
                .map(|class| {
                    class
                        .parse()
                        .map_err(|_| format!("invalid depth-two class {class:?}"))
                })
                .collect::<Result<Vec<usize>, String>>()?;
            TwoClubPartition::DepthTwo {
                base_mod: required_number(&args, "--d2-base")?,
                classes,
                worker,
                workers,
            }
        }
        (None, None, None, Some(worker), Some(workers)) => {
            TwoClubPartition::Worker { worker, workers }
        }
        (None, None, None, None, None) => TwoClubPartition::Whole,
        _ => {
            return Err(
                "partition options require --worker/--workers; depth-two requires both options"
                    .to_owned(),
            );
        }
    };
    let branch_rule = parse_two_club_branch(value(&args, "--branch"))?;
    let mut config = TwoClubConfig {
        max_nodes_per_cell: parse_number(&args, "--max-nodes", 20_000_000)?,
        branch_rule,
        trace: args.flags.contains("--trace"),
        dump_frontier: args.flags.contains("--dump-frontier"),
        sdp: value(&args, "--sdp-worker").map(|worker| TwoClubSdpConfig {
            worker: PathBuf::from(worker),
            instance: instance_path.to_path_buf(),
        }),
        partition,
        ..TwoClubConfig::default()
    };
    config.lp.enabled = !args.flags.contains("--no-lp");
    config.lp.ceiling = !args.flags.contains("--no-lp-ceiling");
    config.lp.warmup = parse_number(&args, "--lp-warmup", config.lp.warmup)?;
    config.lp.cadence = parse_number(&args, "--lp-cadence", config.lp.cadence)?;
    config.lp.window = parse_number(&args, "--lp-window", config.lp.window)?;
    config.lp.max_rows = parse_number(&args, "--lp-max-rows", config.lp.max_rows)?;
    config.lp.low_margin = parse_number(&args, "--lp-low-margin", config.lp.low_margin)?;
    config.lp.exact_margin = parse_number(&args, "--lp-exact-margin", config.lp.exact_margin)?;
    if config.lp.exact_margin < 0 {
        return Err("--lp-exact-margin must be non-negative".to_owned());
    }
    // Strengthened neighborhood rows: default OFF; measured negative on
    // 2club200v15p5scn (see TwoClubLpConfig::nbhd_rows).
    config.lp.nbhd_rows = args.flags.contains("--nbhd-rows");

    eprintln!("two-club config: {config:?}");
    let started = Instant::now();
    let deadline = started
        .checked_add(Duration::from_secs(seconds))
        .ok_or_else(|| "--seconds exceeds the platform clock range".to_owned())?;
    let stop = || Instant::now() >= deadline || ay_sys::process_memory_exceeded();
    let mut best = i128::MAX;
    let mut on_improve = |objective: i128, _assignment: &[bool]| {
        if objective < best {
            best = objective;
            eprintln!("  incumbent {objective} @ {:?}", started.elapsed());
        }
    };
    let outcome = dev_tools::run_two_club(
        &instance,
        objective,
        seed.as_deref(),
        &config,
        &stop,
        &mut on_improve,
    )
    .map_err(|error| error.to_string())?;
    match outcome {
        TwoClubOutcome::Worker { best, all_done } => {
            let (worker, workers) = match config.partition {
                TwoClubPartition::Worker { worker, workers }
                | TwoClubPartition::DepthTwo {
                    worker, workers, ..
                }
                | TwoClubPartition::Pivot {
                    worker, workers, ..
                } => (worker, workers),
                TwoClubPartition::Whole => return Err("internal partition mismatch".to_owned()),
            };
            eprintln!(
                "TWO_CLUB WORKER {worker}/{workers}: Some(({best}, {all_done})) time={:?} \
                 (all_done+best==seed across ALL workers = optimality proof)",
                started.elapsed()
            );
        }
        TwoClubOutcome::Proved {
            objective,
            selected,
        } => eprintln!(
            "TWO_CLUB PROVED: obj={objective} selected={selected} time={:?}",
            started.elapsed()
        ),
        TwoClubOutcome::Cutoff => eprintln!(
            "TWO_CLUB declined/cut after {:?} (best streamed {best})",
            started.elapsed()
        ),
    }
    Ok(())
}

fn probe(args: Vec<String>) -> Result<(), String> {
    let args = parse_args(args, &["--seconds", "--node-budget"], &[])?;
    let [engine, instance_path] = args.positional.as_slice() else {
        return Err("probe requires ENGINE and INSTANCE".to_owned());
    };
    let engine = match engine.as_str() {
        "bnn" => ProbeEngine::Bnn,
        "bnb" => ProbeEngine::BranchAndBound,
        "sls" => ProbeEngine::Sls,
        "card" => ProbeEngine::CardDescent,
        "lp" => ProbeEngine::Lp,
        "safe-lp" => ProbeEngine::SafeLp,
        "milp" => ProbeEngine::Milp,
        "floor" => ProbeEngine::Floor,
        other => return Err(format!("unknown probe engine {other:?}")),
    };
    let instance = read_opb(Path::new(instance_path))?;
    let seconds: u64 = parse_number(&args, "--seconds", 60)?;
    if seconds == 0 {
        return Err("--seconds must be positive".to_owned());
    }
    let started = Instant::now();
    let deadline = started
        .checked_add(Duration::from_secs(seconds))
        .ok_or_else(|| "--seconds exceeds the platform clock range".to_owned())?;
    let stop = || Instant::now() >= deadline;
    let config = ProbeConfig {
        node_budget: parse_number(&args, "--node-budget", 10_000_000)?,
        milp_budget: Duration::from_secs(seconds),
    };
    let mut on_improve = |objective: i128, _assignment: &[bool]| {
        eprintln!("  incumbent {objective} @ {:?}", started.elapsed());
    };
    let outcome = dev_tools::run_probe(&instance, engine, config, &stop, &mut on_improve)
        .map_err(|error| error.to_string())?;
    println!(
        "PROBE {engine:?} {instance_path}: {outcome:?} time={:?}",
        started.elapsed()
    );
    Ok(())
}

fn assert_pbp_structure(
    label: &str,
    instance: &ay_pb::PbInstance,
    proof: &str,
) -> Result<(), String> {
    let input_rows = ay_pb::veripb_input_constraint_count(instance)
        .map_err(|error| format!("{label}: count VeriPB input rows: {error}"))?;
    let formula_declaration = format!("f {input_rows} ;");
    let conclusion_ids: Vec<_> = proof
        .lines()
        .filter_map(|line| {
            line.strip_prefix("conclusion UNSAT : ")
                .and_then(|id| id.strip_suffix(';'))
        })
        .collect();
    if proof.trim().is_empty()
        || !proof.starts_with("pseudo-Boolean proof version 3.0\n")
        || !proof
            .lines()
            .any(|line| line == formula_declaration.as_str())
        || proof.lines().filter(|line| *line == "output NONE;").count() != 1
        || conclusion_ids.len() != 1
        || !conclusion_ids[0]
            .parse::<u64>()
            .is_ok_and(|identifier| identifier > 0)
        || !proof.ends_with("end pseudo-Boolean proof;\n")
    {
        return Err(format!("{label}: malformed or incomplete UNSAT PBP"));
    }
    Ok(())
}

fn atomic_write(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    std::fs::create_dir_all(parent)
        .map_err(|error| format!("create {}: {error}", parent.display()))?;
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| format!("{} has a non-UTF-8 file name", path.display()))?;
    for attempt in 0..100u32 {
        let temporary = parent.join(format!(".{name}.tmp-{}-{attempt}", std::process::id()));
        let mut file = match OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary)
        {
            Ok(file) => file,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(format!("create {}: {error}", temporary.display())),
        };
        let staged = file.write_all(bytes).and_then(|()| file.sync_all());
        drop(file);
        if let Err(error) = staged {
            let _ = std::fs::remove_file(&temporary);
            return Err(format!("write {}: {error}", temporary.display()));
        }
        if let Err(error) = std::fs::rename(&temporary, path) {
            let _ = std::fs::remove_file(&temporary);
            return Err(format!("commit {}: {error}", path.display()));
        }
        return Ok(());
    }
    Err(format!(
        "could not reserve temporary output for {}",
        path.display()
    ))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DeclinePolicy {
    Reject,
    Allow,
}

struct CertifyConfig {
    limit: usize,
    veripb: PathBuf,
    veripb_sha256: String,
    proof_dir: Option<PathBuf>,
    decline_policy: DeclinePolicy,
    minimum_verified: usize,
}

fn digest_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    output
}

fn sha256_file(path: &Path) -> Result<String, String> {
    let mut file =
        std::fs::File::open(path).map_err(|error| format!("open {}: {error}", path.display()))?;
    let mut hasher = Sha256::new();
    let mut buffer = vec![0u8; 64 * 1024];
    loop {
        let count = file
            .read(&mut buffer)
            .map_err(|error| format!("read {}: {error}", path.display()))?;
        if count == 0 {
            break;
        }
        hasher.update(&buffer[..count]);
    }
    Ok(digest_hex(&hasher.finalize()))
}

fn proof_artifact_name(index: usize, path: &Path, proof: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(path.to_string_lossy().as_bytes());
    hasher.update([0]);
    hasher.update(proof.as_bytes());
    let digest = hasher.finalize();
    format!("{index:04}-{}.pbp", digest_hex(&digest[..8]))
}

fn temporary_proof(artifact_name: &str, proof: &str) -> Result<PathBuf, String> {
    for attempt in 0..100u32 {
        let path = std::env::temp_dir().join(format!(
            "ay-pb-dev-veripb-{}-{attempt}-{artifact_name}",
            std::process::id()
        ));
        let mut output = match OpenOptions::new().write(true).create_new(true).open(&path) {
            Ok(output) => output,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(format!("create {}: {error}", path.display())),
        };
        if let Err(error) = output
            .write_all(proof.as_bytes())
            .and_then(|()| output.sync_all())
        {
            drop(output);
            let _ = std::fs::remove_file(&path);
            return Err(format!("write {}: {error}", path.display()));
        }
        return Ok(path);
    }
    Err(format!(
        "could not reserve a temporary proof path for {artifact_name}"
    ))
}

// Debug formatting deliberately escapes paths so an embedded newline cannot
// forge an extra field in this line-oriented verification receipt.
#[allow(clippy::unnecessary_debug_formatting)]
fn verification_sidecar(
    config: &CertifyConfig,
    formula: &Path,
    proof_path: &Path,
    receipt: &ay_pb::veripb_runner::VerifiedUnsat,
    envelope: VeriPbEnvelope,
) -> String {
    format!(
        "VERIPB_VERIFICATION_V1\n\
         verdict=VERIFIED_UNSATISFIABLE\n\
         checker={:?}\n\
         checker_sha256={}\n\
         formula={formula:?}\n\
         proof={proof_path:?}\n\
         elapsed_ms={}\n\
         stdout_retained_bytes={}\n\
         stdout_truncated={}\n\
         stderr_retained_bytes={}\n\
         stderr_truncated={}\n\
         envelope={}\n",
        config.veripb,
        config.veripb_sha256,
        receipt.elapsed().as_millis(),
        receipt.stdout().len(),
        receipt.stdout_truncated(),
        receipt.stderr().len(),
        receipt.stderr_truncated(),
        envelope.record(),
    )
}

fn certify_files(files: &[PathBuf], config: &CertifyConfig) -> Result<(), String> {
    if files.is_empty() {
        return Err("verification campaign found no input files".to_owned());
    }
    if config.limit == 0 || files.len() > config.limit {
        return Err(format!(
            "campaign has {} files but explicit limit is {}",
            files.len(),
            config.limit
        ));
    }
    if config.minimum_verified == 0 {
        return Err("verification campaign threshold must be positive".to_owned());
    }
    if let Some(directory) = &config.proof_dir {
        std::fs::create_dir_all(directory)
            .map_err(|error| format!("create {}: {error}", directory.display()))?;
    }

    let envelope = VeriPbEnvelope::bounded_default();
    println!(
        "VERIPB_ENVELOPE_V1 checker={} checker_sha256={} {}",
        config.veripb.display(),
        config.veripb_sha256,
        envelope.record()
    );

    let mut verified = 0usize;
    let mut declined = 0usize;
    for (index, path) in files.iter().enumerate() {
        let instance = read_opb(path)?;
        let Some(proof) = ay_pb::proof::certify_decision_unsat(&instance) else {
            if config.decline_policy == DeclinePolicy::Allow {
                declined += 1;
                println!("DECLINED {}", path.display());
                continue;
            }
            return Err(format!(
                "{} did not produce UNSAT proof text",
                path.display()
            ));
        };
        assert_pbp_structure(&path.display().to_string(), &instance, &proof)?;

        let artifact_name = proof_artifact_name(index, path, &proof);
        let temporary = temporary_proof(&artifact_name, &proof)?;
        let verification = verify_unsat(&config.veripb, path, &temporary, envelope);
        let cleanup = std::fs::remove_file(&temporary)
            .map_err(|error| format!("remove {}: {error}", temporary.display()));
        let receipt = match (verification, cleanup) {
            (Ok(receipt), Ok(())) => receipt,
            (Ok(_), Err(cleanup_error)) => return Err(cleanup_error),
            (Err(error), Ok(())) => {
                return Err(format!("VeriPB did not verify {}: {error}", path.display()));
            }
            (Err(error), Err(cleanup_error)) => {
                return Err(format!(
                    "VeriPB did not verify {}: {error}; additionally {cleanup_error}",
                    path.display()
                ));
            }
        };
        let checker_sha256_after = sha256_file(&config.veripb)?;
        if checker_sha256_after != config.veripb_sha256 {
            return Err(format!(
                "VeriPB checker changed during the campaign: {}",
                config.veripb.display()
            ));
        }

        let persisted = if let Some(directory) = &config.proof_dir {
            let proof_path = directory.join(&artifact_name);
            atomic_write(&proof_path, proof.as_bytes())?;
            let sidecar_path = directory.join(format!("{artifact_name}.verification.txt"));
            let sidecar = verification_sidecar(config, path, &proof_path, &receipt, envelope);
            atomic_write(&sidecar_path, sidecar.as_bytes())?;
            proof_path.display().to_string()
        } else {
            "ephemeral".to_owned()
        };

        verified += 1;
        println!(
            "VERIFIED {} proof={} bytes={} elapsed_ms={}",
            path.display(),
            persisted,
            proof.len(),
            receipt.elapsed().as_millis()
        );
    }
    if verified < config.minimum_verified {
        return Err(format!(
            "verification campaign produced {verified} VERIFIED result(s); \
             required at least {}",
            config.minimum_verified
        ));
    }
    println!(
        "VERIFICATION CAMPAIGN: {verified}/{} VERIFIED_UNSATISFIABLE, \
         {declined} declined; checker_sha256={}",
        files.len(),
        config.veripb_sha256,
    );
    Ok(())
}

fn cert_config(args: &ParsedArgs, default_limit: usize) -> Result<CertifyConfig, String> {
    let limit = parse_number(args, "--limit", default_limit)?;
    if limit == 0 {
        return Err("--limit must be positive".to_owned());
    }
    let veripb = PathBuf::from(
        value(args, "--veripb")
            .ok_or_else(|| "--veripb FILE is required for every certify-* command".to_owned())?,
    );
    if !veripb.is_file() {
        return Err(format!("--veripb is not a file: {}", veripb.display()));
    }
    let veripb_sha256 = sha256_file(&veripb)?;
    Ok(CertifyConfig {
        limit,
        veripb,
        veripb_sha256,
        proof_dir: value(args, "--proof-dir").map(PathBuf::from),
        decline_policy: DeclinePolicy::Reject,
        minimum_verified: 1,
    })
}

fn certify_unsat(args: Vec<String>) -> Result<(), String> {
    let args = parse_args(args, &["--limit", "--veripb", "--proof-dir"], &[])?;
    let config = cert_config(&args, 32)?;
    let files: Vec<PathBuf> = args.positional.iter().map(PathBuf::from).collect();
    certify_files(&files, &config)
}

fn collect_matching_files(
    root: &Path,
    needle: &str,
    limit: usize,
    output: &mut Vec<PathBuf>,
) -> Result<(), String> {
    if output.len() >= limit {
        return Ok(());
    }
    let mut entries: Vec<_> = std::fs::read_dir(root)
        .map_err(|error| format!("read directory {}: {error}", root.display()))?
        .collect::<Result<_, _>>()
        .map_err(|error| format!("read directory entry under {}: {error}", root.display()))?;
    entries.sort_by_key(std::fs::DirEntry::path);
    for entry in entries {
        if output.len() >= limit {
            break;
        }
        let path = entry.path();
        let file_type = entry
            .file_type()
            .map_err(|error| format!("inspect {}: {error}", path.display()))?;
        if file_type.is_dir() {
            collect_matching_files(&path, needle, limit, output)?;
        } else if file_type.is_file() {
            let display = path.to_string_lossy().to_ascii_lowercase();
            if display.contains(needle) && display.contains(".opb") {
                output.push(path);
            }
        }
    }
    Ok(())
}

fn certify_koops(args: Vec<String>) -> Result<(), String> {
    let args = parse_args(
        args,
        &["--limit", "--match", "--veripb", "--proof-dir"],
        &[],
    )?;
    let [root] = args.positional.as_slice() else {
        return Err("certify-koops requires exactly one ROOT".to_owned());
    };
    let mut config = cert_config(&args, 1)?;
    config.limit = required_number(&args, "--limit")?;
    if config.limit == 0 {
        return Err("--limit must be positive".to_owned());
    }
    let needle = value(&args, "--match")
        .unwrap_or("koops")
        .to_ascii_lowercase();
    config.decline_policy = if needle.contains("mat98") {
        DeclinePolicy::Reject
    } else {
        DeclinePolicy::Allow
    };
    let mut files = Vec::new();
    collect_matching_files(Path::new(root), &needle, config.limit, &mut files)?;
    certify_files(&files, &config)
}

fn certify_mat98(args: Vec<String>) -> Result<(), String> {
    let args = parse_args(args, &["--veripb", "--proof-dir"], &[])?;
    let [file] = args.positional.as_slice() else {
        return Err("certify-mat98 requires exactly one FILE".to_owned());
    };
    let config = cert_config(&args, 1)?;
    certify_files(&[PathBuf::from(file)], &config)
}

fn farkas_anchor(args: Vec<String>) -> Result<(), String> {
    let args = parse_args(args, &[], &[])?;
    let [output_dir] = args.positional.as_slice() else {
        return Err("farkas-anchor requires exactly one OUTPUT_DIR".to_owned());
    };
    let paths =
        dev_tools::write_farkas_anchor(Path::new(output_dir)).map_err(|error| error.to_string())?;
    println!(
        "FARKAS ANCHOR: valid={} tampered={}",
        paths.valid.display(),
        paths.tampered.display()
    );
    Ok(())
}

fn export_wbo(args: Vec<String>) -> Result<(), String> {
    let args = parse_args(args, &[], &[])?;
    let [input, output] = args.positional.as_slice() else {
        return Err("export-wbo requires INPUT and OUTPUT".to_owned());
    };
    let text = std::fs::read_to_string(input).map_err(|error| format!("read {input}: {error}"))?;
    let wbo = ay_pb::parse_wbo(&text).map_err(|error| format!("parse {input}: {error}"))?;
    let projected =
        ay_pb::try_wbo_to_pbo(&wbo).map_err(|error| format!("project {input}: {error}"))?;
    atomic_write(
        Path::new(output),
        ay_pb::instance_to_opb(&projected).as_bytes(),
    )
}

fn export_nlc(args: Vec<String>) -> Result<(), String> {
    let args = parse_args(args, &[], &[])?;
    let [input, output] = args.positional.as_slice() else {
        return Err("export-nlc requires INPUT and OUTPUT".to_owned());
    };
    let instance = read_opb(Path::new(input))?;
    let linear = ay_pb::linearize(&instance);
    atomic_write(
        Path::new(output),
        ay_pb::instance_to_opb(&linear).as_bytes(),
    )
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args().skip(1);
    let command = arguments.next().ok_or_else(|| USAGE.to_owned())?;
    let arguments: Vec<String> = arguments.collect();
    match command.as_str() {
        "two-club" => two_club(arguments),
        "probe" => probe(arguments),
        "certify-unsat" => certify_unsat(arguments),
        "certify-koops" => certify_koops(arguments),
        "certify-mat98" => certify_mat98(arguments),
        "farkas-anchor" => farkas_anchor(arguments),
        "export-wbo" => export_wbo(arguments),
        "export-nlc" => export_nlc(arguments),
        "--help" | "-h" | "help" => {
            print!("{USAGE}");
            Ok(())
        }
        other => Err(format!("unknown command {other:?}\n\n{USAGE}")),
    }
}

fn main() {
    // FIRST statement of main: arm() re-execs this process under a kernel-held
    // memory bound, so anything above it is discarded work, and it sets an env
    // var (sound only while single-threaded). See crates/ay-sys/src/govern.rs.
    ay_sys::govern::arm();

    apply_memory_limit();
    if let Err(error) = run() {
        eprintln!("ay-pb-dev: {error}");
        std::process::exit(2);
    }
}

#[cfg(test)]
mod tests {
    use super::{parse_two_club_branch, TwoClubBranchRule};

    #[test]
    fn two_club_branch_parser_is_closed_and_defaults_to_first() {
        assert_eq!(
            parse_two_club_branch(None).expect("default branch"),
            TwoClubBranchRule::First
        );
        for (raw, expected) in [
            ("first", TwoClubBranchRule::First),
            ("viol", TwoClubBranchRule::ViolatingDegree),
            ("marked", TwoClubBranchRule::Marked),
        ] {
            assert_eq!(
                parse_two_club_branch(Some(raw)).expect("supported branch"),
                expected
            );
        }
        for raw in ["", "FIRST", "mark", "marked "] {
            assert!(parse_two_club_branch(Some(raw)).is_err());
        }
    }
}
