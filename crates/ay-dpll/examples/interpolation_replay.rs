// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded replay tool for captured interpolation queries (QF_LIA / QF_LRA).
//!
//! The assertions of `--file` are split into consecutive GROUPS
//! (`--groups n1,n2,...`, or the legacy two-group `--a-count N`); every
//! `--mask` (bit `g` set = group `g` is on the A side; default: every proper
//! prefix) is interpolated with every requested strength, and each produced
//! interpolant is checked for all three Craig conditions: `A /\ not(I)` and
//! `I /\ B` are both UNSAT, and `I` mentions no symbol exclusive to either
//! side.
//!
//! ```text
//! cargo run -p ay-dpll --release --example interpolation_replay -- \
//!   --file capture.smt2 --a-count 40                         # legacy, QF_LIA
//! cargo run -p ay-dpll --release --example interpolation_replay -- \
//!   --file q.smt2 --logic QF_LRA --groups 125,42 --mask 1 \
//!   --mode explicit --proof-mode interpolation --plain-solve --json \
//!   --dump-dir out/
//! ```
//!
//! `--mode explicit` uses the fail-closed extractor
//! (`Solver::get_interpolants_for_masks`, Workstream D Rung 1) and reports the
//! failure kind and the offending proof step; `--mode legacy` (the default)
//! is the historical traversal. `--proof-mode required` makes the proof a
//! required artifact (`set_produce_proofs(true)`); `best-effort` retains the
//! internal proof without making its strict translation verdict-relevant;
//! `interpolation` records it for the interpolation extractor only
//! (`set_interpolation_proofs`, what the CHC engines use for QF_LRA).
//! `--plain-solve` first times the same script without proof production (the
//! `c_s` of the `c_p/c_s` ratio). `--json` prints one JSON object with the
//! verdicts, times, the reachable-proof census (rules, Trust steps, lemma
//! kinds) and one record per (mask, strength). `--dump-dir` writes every
//! interpolant as DAG-linear `define-fun`s ending in `(define-fun __itp ()
//! Bool …)` for an external (z3) re-check.
//!
//! Each solve has a 30-second default timeout, input is capped at 16 MiB, and
//! solver/term memory have fixed 2 GiB/512 MiB ceilings. The timeout and input
//! cap can be adjusted explicitly without relying on process environment.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use ay_core::{AletheRule, ProofStep};
use ay_dpll::api::{
    split_leading_set_logic, InterpolantMode, InterpolantStrength, Logic, Solver, SolverConfig,
    SolverError, Sort, Term, TermKind, VerifiedSolveResult,
};
use ay_frontend::Command;

const DEFAULT_TIMEOUT_SECONDS: u64 = 30;
const DEFAULT_MAX_INPUT_BYTES: usize = 16 * 1024 * 1024;
const SOLVER_MEMORY_LIMIT_BYTES: usize = 2 * 1024 * 1024 * 1024;
const TERM_MEMORY_LIMIT_BYTES: usize = 512 * 1024 * 1024;
const BEST_EFFORT_STEP_BUDGET: u64 = 50_000_000;

#[derive(Clone, Copy, PartialEq, Eq)]
enum ProofMode {
    Required,
    BestEffort,
    Interpolation,
}

struct Args {
    file: PathBuf,
    a_count: Option<usize>,
    groups: Option<Vec<usize>>,
    masks: Vec<u128>,
    logic: Option<Logic>,
    mode: InterpolantMode,
    strengths: Vec<(&'static str, InterpolantStrength)>,
    proof_mode: ProofMode,
    plain_solve: bool,
    json: bool,
    dump_dir: Option<PathBuf>,
    trust_samples: usize,
    timeout_seconds: u64,
    max_input_bytes: usize,
}

/// One extracted interpolant (or failure) for a (mask, strength) pair.
struct Record {
    mask: u128,
    strength: &'static str,
    extract_secs: f64,
    outcome: Result<Candidate, Failure>,
}

struct Candidate {
    term: Term,
    shared_symbols_only: bool,
    dag_nodes: usize,
    dump: Option<PathBuf>,
    checks: Option<(String, String)>,
}

struct Failure {
    kind: String,
    step: Option<usize>,
    step_desc: Option<String>,
}

fn usage() -> &'static str {
    "usage: interpolation_replay --file FILE (--a-count N | --groups N1,N2,...) \
     [--mask M]... [--logic QF_LIA|QF_LRA] [--mode legacy|explicit] \
     [--strength all|weakest|default|strongest] [--proof-mode required|best-effort|interpolation] \
     [--plain-solve] [--json] [--dump-dir DIR] [--trust-samples N] [--timeout-seconds N] \
     [--max-input-bytes N]"
}

fn next_value(args: &mut impl Iterator<Item = String>, option: &str) -> Result<String, String> {
    args.next()
        .ok_or_else(|| format!("missing value for {option}\n{}", usage()))
}

fn parse_num<T: std::str::FromStr>(raw: &str, option: &str) -> Result<T, String> {
    raw.parse()
        .map_err(|_| format!("invalid {option} value `{raw}`"))
}

fn parse_args() -> Result<Option<Args>, String> {
    let mut file = None;
    let mut a_count = None;
    let mut groups = None;
    let mut masks = Vec::new();
    let mut logic = None;
    let mut mode = InterpolantMode::Legacy;
    let mut strength_sel = "all".to_string();
    let mut proof_mode = ProofMode::Required;
    let mut plain_solve = false;
    let mut json = false;
    let mut dump_dir = None;
    let mut trust_samples = 0usize;
    let mut timeout_seconds = DEFAULT_TIMEOUT_SECONDS;
    let mut max_input_bytes = DEFAULT_MAX_INPUT_BYTES;
    let mut args = std::env::args().skip(1);

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--file" => file = Some(PathBuf::from(next_value(&mut args, "--file")?)),
            "--a-count" => {
                a_count = Some(parse_num(
                    &next_value(&mut args, "--a-count")?,
                    "--a-count",
                )?);
            }
            "--groups" => {
                let raw = next_value(&mut args, "--groups")?;
                let sizes: Result<Vec<usize>, String> = raw
                    .split(',')
                    .map(|s| parse_num(s.trim(), "--groups"))
                    .collect();
                groups = Some(sizes?);
            }
            "--mask" => masks.push(parse_num(&next_value(&mut args, "--mask")?, "--mask")?),
            "--logic" => {
                logic = Some(match next_value(&mut args, "--logic")?.as_str() {
                    "QF_LIA" => Logic::QfLia,
                    "QF_LRA" => Logic::QfLra,
                    other => return Err(format!("unsupported --logic `{other}`")),
                });
            }
            "--mode" => {
                mode = match next_value(&mut args, "--mode")?.as_str() {
                    "legacy" => InterpolantMode::Legacy,
                    "explicit" => InterpolantMode::Explicit,
                    other => return Err(format!("unsupported --mode `{other}`")),
                };
            }
            "--strength" => strength_sel = next_value(&mut args, "--strength")?,
            "--proof-mode" => {
                proof_mode = match next_value(&mut args, "--proof-mode")?.as_str() {
                    "required" => ProofMode::Required,
                    "best-effort" => ProofMode::BestEffort,
                    "interpolation" => ProofMode::Interpolation,
                    other => return Err(format!("unsupported --proof-mode `{other}`")),
                };
            }
            "--plain-solve" => plain_solve = true,
            "--json" => json = true,
            "--dump-dir" => dump_dir = Some(PathBuf::from(next_value(&mut args, "--dump-dir")?)),
            "--trust-samples" => {
                trust_samples = parse_num(
                    &next_value(&mut args, "--trust-samples")?,
                    "--trust-samples",
                )?;
            }
            "--timeout-seconds" => {
                timeout_seconds = parse_num(
                    &next_value(&mut args, "--timeout-seconds")?,
                    "--timeout-seconds",
                )?;
            }
            "--max-input-bytes" => {
                max_input_bytes = parse_num(
                    &next_value(&mut args, "--max-input-bytes")?,
                    "--max-input-bytes",
                )?;
            }
            "-h" | "--help" => {
                println!("{}", usage());
                return Ok(None);
            }
            _ => return Err(format!("unknown argument `{arg}`\n{}", usage())),
        }
    }

    if timeout_seconds == 0 {
        return Err("--timeout-seconds must be positive".to_string());
    }
    if max_input_bytes == 0 {
        return Err("--max-input-bytes must be positive".to_string());
    }
    if a_count.is_some() == groups.is_some() {
        return Err(format!(
            "exactly one of --a-count and --groups is required\n{}",
            usage()
        ));
    }
    let all = [
        ("weakest", InterpolantStrength::Weakest),
        ("default", InterpolantStrength::Default),
        ("strongest", InterpolantStrength::Strongest),
    ];
    let strengths: Vec<_> = match strength_sel.as_str() {
        "all" => all.to_vec(),
        name => {
            let picked: Vec<_> = all.iter().copied().filter(|(n, _)| *n == name).collect();
            if picked.is_empty() {
                return Err(format!("unsupported --strength `{name}`"));
            }
            picked
        }
    };

    Ok(Some(Args {
        file: file.ok_or_else(|| format!("--file is required\n{}", usage()))?,
        a_count,
        groups,
        masks,
        logic,
        mode,
        strengths,
        proof_mode,
        plain_solve,
        json,
        dump_dir,
        trust_samples,
        timeout_seconds,
        max_input_bytes,
    }))
}

fn read_bounded(path: &Path, max_bytes: usize) -> Result<String, Box<dyn std::error::Error>> {
    let read_limit = max_bytes
        .checked_add(1)
        .ok_or("--max-input-bytes is too large")?;
    let read_limit = u64::try_from(read_limit).map_err(|_| "--max-input-bytes is too large")?;
    let mut bytes = Vec::new();
    File::open(path)?.take(read_limit).read_to_end(&mut bytes)?;
    if bytes.len() > max_bytes {
        return Err(format!(
            "{} exceeds the configured {}-byte input limit",
            path.display(),
            max_bytes
        )
        .into());
    }
    Ok(String::from_utf8(bytes)?)
}

/// Drop query/exit commands (one command per line in captured scripts), so
/// parsing only declares and asserts.
fn strip_queries(source: &str) -> String {
    source
        .lines()
        .filter(|line| {
            let t = line.trim_start();
            !(t.starts_with("(check-sat") || t.starts_with("(exit") || t.starts_with("(get-"))
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn check_conjunction(
    solver: &mut Solver,
    partition: &[Term],
    extra: Term,
) -> Result<VerifiedSolveResult, SolverError> {
    solver.try_reset_assertions()?;
    for &term in partition {
        solver.try_assert_term(term)?;
    }
    solver.try_assert_term(extra)?;
    Ok(solver.check_sat())
}

fn declared_value_names(source: &str) -> Result<HashSet<String>, Box<dyn std::error::Error>> {
    let mut names = HashSet::new();
    for command in ay_frontend::parse(source)? {
        match command {
            Command::DeclareFun(name, ..)
            | Command::DeclareConst(name, ..)
            | Command::DeclareVar(name, ..)
            | Command::DeclareRel(name, ..)
            | Command::DefineFun(name, ..)
            | Command::DefineFunRec(name, ..) => {
                names.insert(name);
            }
            _ => {}
        }
    }
    Ok(names)
}

fn partition_exclusive_names(
    solver: &Solver,
    a_terms: &[Term],
    b_terms: &[Term],
    declared_names: &HashSet<String>,
) -> HashSet<String> {
    declared_names
        .iter()
        .filter(|name| {
            let singleton = HashSet::from([(*name).clone()]);
            solver.terms_mention_names(a_terms, &singleton)
                != solver.terms_mention_names(b_terms, &singleton)
        })
        .cloned()
        .collect()
}

fn verdict_name(result: &VerifiedSolveResult) -> &'static str {
    if result.is_unsat() {
        "unsat"
    } else if result.is_sat() {
        "sat"
    } else {
        "unknown"
    }
}

fn sort_name(sort: &Sort) -> Option<&'static str> {
    match sort {
        Sort::Bool => Some("Bool"),
        Sort::Int => Some("Int"),
        Sort::Real => Some("Real"),
        _ => None,
    }
}

/// DAG-linear SMT-LIB rendering: one `define-fun` per compound node (children
/// first), then `(define-fun __itp () Bool <root>)`. Returns the text and the
/// number of distinct compound nodes.
fn dag_define_funs(solver: &Solver, root: Term) -> Result<(String, usize), String> {
    let mut names: HashMap<Term, String> = HashMap::new();
    let mut out = String::new();
    let mut stack: Vec<(Term, bool)> = vec![(root, false)];
    let mut defined = 0usize;
    while let Some((t, expanded)) = stack.pop() {
        if names.contains_key(&t) {
            continue;
        }
        let kind = solver.term_kind(t);
        match kind {
            TermKind::Var { .. } | TermKind::Const => {
                names.insert(t, solver.format_term(t));
                continue;
            }
            _ => {}
        }
        let children = solver.term_children(t);
        if !expanded {
            stack.push((t, true));
            for &c in children.iter().rev() {
                if !names.contains_key(&c) {
                    stack.push((c, false));
                }
            }
            continue;
        }
        let head = match kind {
            TermKind::App { name, .. } => name,
            TermKind::Not => "not".to_string(),
            TermKind::Ite => "ite".to_string(),
            _ => return Err("binder in interpolant".to_string()),
        };
        let sort = solver.term_sort(t);
        let sort = sort_name(&sort).ok_or_else(|| format!("unsupported sort {sort:?}"))?;
        let mut body = format!("({head}");
        for c in &children {
            body.push(' ');
            body.push_str(names.get(c).ok_or("child not rendered")?);
        }
        body.push(')');
        let name = format!("__i{defined}");
        defined += 1;
        out.push_str(&format!("(define-fun {name} () {sort} {body})\n"));
        names.insert(t, name);
    }
    let root_name = names.get(&root).ok_or("root not rendered")?;
    out.push_str(&format!("(define-fun __itp () Bool {root_name})\n"));
    Ok((out, defined))
}

fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Reachable-proof census of the refutation Explicit extraction reads: rule/kind
/// histogram, Trust steps, lemma kinds, and the descriptions of up to `samples`
/// reachable Trust/Hole steps and uncertified `Generic` lemmas (for
/// root-causing where Trust comes from).
fn proof_census(solver: &Solver, samples: usize) -> String {
    let Some(proof) = solver.explicit_interpolation_proof() else {
        return "null".to_string();
    };
    let n = proof.steps.len();
    let mut seen = vec![false; n];
    let mut stack: Vec<usize> = n.checked_sub(1).into_iter().collect();
    for &s in &stack {
        seen[s] = true;
    }
    while let Some(i) = stack.pop() {
        let premises: Vec<usize> = match &proof.steps[i] {
            ProofStep::Resolution {
                clause1, clause2, ..
            } => vec![clause1.0 as usize, clause2.0 as usize],
            ProofStep::Step { premises, .. } => premises.iter().map(|p| p.0 as usize).collect(),
            ProofStep::Anchor { end_step, .. } => vec![end_step.0 as usize],
            _ => Vec::new(),
        };
        for p in premises {
            if p < n && !seen[p] {
                seen[p] = true;
                stack.push(p);
            }
        }
    }
    let mut hist: BTreeMap<String, usize> = BTreeMap::new();
    let (mut trust_all, mut trust_reach, mut generic, mut farkas, mut lemmas) = (0, 0, 0, 0, 0);
    let mut sample_ids: Vec<usize> = Vec::new();
    for (i, step) in proof.steps.iter().enumerate() {
        let is_trust = matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Trust | AletheRule::Hole,
                ..
            }
        );
        trust_all += usize::from(is_trust);
        if !seen[i] {
            continue;
        }
        trust_reach += usize::from(is_trust);
        let is_generic = matches!(
            step,
            ProofStep::TheoryLemma { kind, farkas: None, .. } if kind.is_trust()
        );
        if (is_trust || is_generic) && sample_ids.len() < samples {
            sample_ids.push(i);
        }
        let key = match step {
            ProofStep::Assume(_) => "assume".to_string(),
            ProofStep::Resolution { .. } => "resolution".to_string(),
            ProofStep::TheoryLemma {
                kind, farkas: f, ..
            } => {
                lemmas += 1;
                farkas += usize::from(f.is_some());
                generic += usize::from(kind.is_trust() && f.is_none());
                format!(
                    "lemma:{}{}",
                    kind.alethe_rule(),
                    if f.is_some() { "+farkas" } else { "" }
                )
            }
            ProofStep::Step { rule, premises, .. } => {
                format!("step:{}/{}", rule.name(), premises.len().min(2))
            }
            ProofStep::Anchor { .. } => "anchor".to_string(),
            _ => "other".to_string(),
        };
        *hist.entry(key).or_default() += 1;
    }
    let hist_json: Vec<String> = hist
        .iter()
        .map(|(k, v)| format!("{}:{v}", json_str(k)))
        .collect();
    let sample_json: Vec<String> = sample_ids
        .iter()
        .map(|&i| {
            let desc = solver
                .describe_last_proof_step(i)
                .unwrap_or_default()
                .chars()
                .take(600)
                .collect::<String>();
            format!("{{\"step\":{i},\"desc\":{}}}", json_str(&desc))
        })
        .collect();
    format!(
        "{{\"steps\":{n},\"reachable\":{},\"trust_reachable\":{trust_reach},\"trust_all\":{trust_all},\
         \"lemmas\":{lemmas},\"lemmas_with_farkas\":{farkas},\"generic_lemmas_uncertified\":{generic},\
         \"rules\":{{{}}},\"trust_samples\":[{}]}}",
        seen.iter().filter(|s| **s).count(),
        hist_json.join(","),
        sample_json.join(",")
    )
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let Some(args) = parse_args()? else {
        return Ok(());
    };
    let raw = read_bounded(&args.file, args.max_input_bytes)?;
    let (script_logic, body) = split_leading_set_logic(&raw, Logic::QfLia);
    let logic = args.logic.unwrap_or(script_logic);
    let source = strip_queries(body.as_ref());
    let config = SolverConfig::default()
        .with_timeout(Duration::from_secs(args.timeout_seconds))
        .with_memory_limit(SOLVER_MEMORY_LIMIT_BYTES)
        .with_term_memory_limit(TERM_MEMORY_LIMIT_BYTES);

    // c_s: the same script without proof production.
    let plain = if args.plain_solve {
        let mut plain = Solver::try_new_with_config(logic, config.clone())?;
        plain.parse_smtlib2(&source)?;
        let t0 = Instant::now();
        let result = plain.check_sat_internal_query();
        Some((verdict_name(&result), t0.elapsed().as_secs_f64()))
    } else {
        None
    };

    let mut solver = Solver::try_new_with_config(logic, config)?;
    let enable_proofs = |solver: &mut Solver| {
        match args.proof_mode {
            ProofMode::Required => solver.set_produce_proofs(true),
            ProofMode::BestEffort => solver.set_best_effort_produce_proofs(BEST_EFFORT_STEP_BUDGET),
            ProofMode::Interpolation => solver.set_interpolation_proofs(BEST_EFFORT_STEP_BUDGET),
        }
        solver.set_option(":ay-proof-no-varsubst", "true");
    };
    enable_proofs(&mut solver);
    let assertions = solver.parse_smtlib2(&source)?;
    // Reassert the proof settings after parsing so capture-local options
    // cannot disable the interpolation path.
    enable_proofs(&mut solver);

    let sizes: Vec<usize> = match (&args.groups, args.a_count) {
        (Some(sizes), _) => sizes.clone(),
        (None, Some(a)) => {
            if a == 0 || a >= assertions.len() {
                return Err(format!(
                    "--a-count must split {} assertions into nonempty A and B partitions",
                    assertions.len()
                )
                .into());
            }
            vec![a, assertions.len() - a]
        }
        (None, None) => unreachable!("parse_args requires one of them"),
    };
    if sizes.iter().sum::<usize>() != assertions.len() || sizes.contains(&0) {
        return Err(format!(
            "--groups {sizes:?} do not partition {} assertions",
            assertions.len()
        )
        .into());
    }
    let mut groups: Vec<Vec<Term>> = Vec::with_capacity(sizes.len());
    let mut at = 0;
    for &n in &sizes {
        groups.push(assertions[at..at + n].to_vec());
        at += n;
    }
    let masks: Vec<u128> = if args.masks.is_empty() {
        (1..sizes.len()).map(|i| (1u128 << i) - 1).collect()
    } else {
        args.masks.clone()
    };

    let t0 = Instant::now();
    let result = solver.check_sat_internal_query();
    let proof_secs = t0.elapsed().as_secs_f64();
    let verdict = verdict_name(&result);
    let census = if result.is_unsat() {
        proof_census(&solver, args.trust_samples)
    } else {
        "null".to_string()
    };
    let trust_steps = solver.last_proof_trust_steps();
    let proof_decline = result
        .is_unsat()
        .then(|| solver.last_proof_decline().map(|m| m.tag()))
        .flatten();

    let group_slices: Vec<&[Term]> = groups.iter().map(Vec::as_slice).collect();
    let mut records: Vec<Record> = Vec::new();
    if result.is_unsat() {
        for &mask in &masks {
            for &(name, strength) in &args.strengths {
                let t = Instant::now();
                let outcome = match args.mode {
                    InterpolantMode::Explicit => solver
                        .get_interpolants_for_masks(&group_slices, &[mask], strength, args.mode)
                        .map(|v| v[0])
                        .map_err(|e| Failure {
                            kind: e.kind_name().to_string(),
                            step: e.step(),
                            step_desc: e
                                .step()
                                .and_then(|s| solver.describe_last_proof_step(s))
                                .or_else(|| Some(e.to_string())),
                        }),
                    _ => {
                        let (a, b) = split_by_mask(&groups, mask);
                        solver
                            .get_interpolant_with_strength(&a, &b, strength)
                            .map(|r| r.interpolant())
                            .ok_or(Failure {
                                kind: "legacy_none".to_string(),
                                step: None,
                                step_desc: None,
                            })
                    }
                };
                let extract_secs = t.elapsed().as_secs_f64();
                records.push(Record {
                    mask,
                    strength: name,
                    extract_secs,
                    outcome: outcome.map(|term| Candidate {
                        term,
                        shared_symbols_only: false,
                        dag_nodes: 0,
                        dump: None,
                        checks: None,
                    }),
                });
            }
        }
    }

    // Symbol locality, dumps, then the Craig checks (verification solves do
    // not record proofs; they reset the assertion stack).
    let declared = declared_value_names(&source)?;
    let stem = args
        .file
        .file_stem()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| "query".to_string());
    for record in &mut records {
        let Ok(candidate) = &mut record.outcome else {
            continue;
        };
        let (a, b) = split_by_mask(&groups, record.mask);
        let exclusive = partition_exclusive_names(&solver, &a, &b, &declared);
        candidate.shared_symbols_only = !solver.terms_mention_names(&[candidate.term], &exclusive);
        if let Some(dir) = &args.dump_dir {
            match dag_define_funs(&solver, candidate.term) {
                Ok((text, nodes)) => {
                    candidate.dag_nodes = nodes;
                    std::fs::create_dir_all(dir)?;
                    let path = dir.join(format!(
                        "{stem}.m{}.{}.itp.smt2",
                        record.mask, record.strength
                    ));
                    std::fs::write(&path, text)?;
                    candidate.dump = Some(path);
                }
                Err(e) => eprintln!("dump failed for mask {}: {e}", record.mask),
            }
        }
    }
    solver.set_produce_proofs(false);
    for record in &mut records {
        let Ok(candidate) = &mut record.outcome else {
            continue;
        };
        let (a, b) = split_by_mask(&groups, record.mask);
        let not_i = solver.try_not(candidate.term)?;
        let a_result = check_conjunction(&mut solver, &a, not_i)?;
        let b_result = check_conjunction(&mut solver, &b, candidate.term)?;
        candidate.checks = Some((
            verdict_name(&a_result).to_string(),
            verdict_name(&b_result).to_string(),
        ));
    }

    if args.json {
        print_json(
            &args,
            logic,
            verdict,
            proof_secs,
            plain,
            &census,
            trust_steps,
            proof_decline,
            &records,
        );
        return Ok(());
    }

    if let Some((v, s)) = plain {
        println!("plain: {v} {s:.3}s");
    }
    println!(
        "proof: {verdict} {proof_secs:.3}s trust_steps={}",
        trust_steps.map_or_else(|| "n/a".to_string(), |t| t.to_string())
    );
    if !result.is_unsat() {
        return Err(format!("interpolation input must be UNSAT, got {result:?}").into());
    }
    let mut failures = Vec::new();
    for record in &records {
        match &record.outcome {
            Ok(candidate) => {
                let (a_v, b_v) = candidate.checks.clone().unwrap_or_default();
                let verified = a_v == "unsat" && b_v == "unsat" && candidate.shared_symbols_only;
                println!(
                    "mask={} {}: A&!I={a_v} I&B={b_v} shared-symbols={} verified={verified} extract={:.3}s",
                    record.mask, record.strength, candidate.shared_symbols_only, record.extract_secs
                );
                if !args.json && candidate.dag_nodes == 0 {
                    println!(
                        "mask={} {}: I = {}",
                        record.mask,
                        record.strength,
                        solver.format_term(candidate.term)
                    );
                }
                if !verified {
                    failures.push(format!(
                        "mask={} {}: Craig verification failed (A&!I={a_v}, I&B={b_v}, \
                         shared-symbols={})",
                        record.mask, record.strength, candidate.shared_symbols_only
                    ));
                }
            }
            Err(failure) => {
                println!(
                    "mask={} {}: FAILED {} step={:?} {}",
                    record.mask,
                    record.strength,
                    failure.kind,
                    failure.step,
                    failure.step_desc.as_deref().unwrap_or("")
                );
                failures.push(format!(
                    "mask={} {}: interpolation returned no candidate ({})",
                    record.mask, record.strength, failure.kind
                ));
            }
        }
    }
    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures.join("; ").into())
    }
}

fn split_by_mask(groups: &[Vec<Term>], mask: u128) -> (Vec<Term>, Vec<Term>) {
    let mut a = Vec::new();
    let mut b = Vec::new();
    for (g, terms) in groups.iter().enumerate() {
        if g < 128 && mask & (1u128 << g) != 0 {
            a.extend_from_slice(terms);
        } else {
            b.extend_from_slice(terms);
        }
    }
    (a, b)
}

#[allow(clippy::too_many_arguments)]
fn print_json(
    args: &Args,
    logic: Logic,
    verdict: &str,
    proof_secs: f64,
    plain: Option<(&str, f64)>,
    census: &str,
    trust_steps: Option<usize>,
    proof_decline: Option<&str>,
    records: &[Record],
) {
    let recs: Vec<String> = records
        .iter()
        .map(|r| match &r.outcome {
            Ok(c) => {
                let (a_v, b_v) = c.checks.clone().unwrap_or_default();
                format!(
                    "{{\"mask\":{},\"strength\":{},\"ok\":true,\"extract_secs\":{:.6},\
                     \"a_not_i\":{},\"i_and_b\":{},\"shared_symbols_only\":{},\"dag_nodes\":{},\"dump\":{}}}",
                    r.mask,
                    json_str(r.strength),
                    r.extract_secs,
                    json_str(&a_v),
                    json_str(&b_v),
                    c.shared_symbols_only,
                    c.dag_nodes,
                    c.dump
                        .as_ref()
                        .map_or_else(|| "null".to_string(), |p| json_str(&p.to_string_lossy()))
                )
            }
            Err(f) => format!(
                "{{\"mask\":{},\"strength\":{},\"ok\":false,\"extract_secs\":{:.6},\
                 \"failure\":{},\"step\":{},\"step_desc\":{}}}",
                r.mask,
                json_str(r.strength),
                r.extract_secs,
                json_str(&f.kind),
                f.step.map_or_else(|| "null".to_string(), |s| s.to_string()),
                f.step_desc
                    .as_deref()
                    .map_or_else(|| "null".to_string(), json_str)
            ),
        })
        .collect();
    println!(
        "{{\"file\":{},\"logic\":{},\"mode\":{},\"proof_mode\":{},\"verdict\":{},\"proof_secs\":{proof_secs:.6},\
         \"plain\":{},\"plain_secs\":{},\"trust_steps\":{},\"proof_decline\":{},\"census\":{census},\"records\":[{}]}}",
        json_str(&args.file.to_string_lossy()),
        json_str(match logic {
            Logic::QfLra => "QF_LRA",
            Logic::QfLia => "QF_LIA",
            _ => "other",
        }),
        json_str(match args.mode {
            InterpolantMode::Explicit => "explicit",
            _ => "legacy",
        }),
        json_str(match args.proof_mode {
            ProofMode::Required => "required",
            ProofMode::BestEffort => "best-effort",
            ProofMode::Interpolation => "interpolation",
        }),
        json_str(verdict),
        plain.map_or_else(|| "null".to_string(), |(v, _)| json_str(v)),
        plain.map_or_else(|| "null".to_string(), |(_, s)| format!("{s:.6}")),
        trust_steps.map_or_else(|| "null".to_string(), |t| t.to_string()),
        proof_decline.map_or_else(|| "null".to_string(), json_str),
        recs.join(",")
    );
}
