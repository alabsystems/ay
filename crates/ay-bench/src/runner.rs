// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eval runner: discovers evals from the YAML registry, executes benchmarks
//! natively in Rust, and applies competition-standard scoring.

use crate::error::{BenchError, Result, WithContext};
use std::collections::BTreeMap;
use std::io::Write as _;
use std::path::{Path, PathBuf};

use crate::db::{ResultRow, ResultsStore, StorePath};
use crate::scoring::{self, Competition, ResultsFile};

// ===================================================================
// Eval registry
// ===================================================================

/// Minimal YAML eval spec — we only need a few fields.
#[derive(Debug)]
struct EvalSpec {
    id: Option<String>,
    competition: Option<String>,
    scoring: Option<String>,
    inputs: Option<EvalInputs>,
}

#[derive(Debug)]
struct EvalInputs {
    timeout_sec: Option<f64>,
    benchmarks_dir: Option<String>,
    /// Text file listing benchmark paths, one per line (e.g., SAT heldout set).
    list_file: Option<String>,
    /// Set manifest file relative to benchmarks_dir (e.g., CHC-COMP LIA.set).
    set_file: Option<String>,
    /// Number of runs per benchmark for statistical reliability.
    runs: Option<u32>,
    /// Subdirectories to scope discovery to (e.g., QF_BV, QF_LIA).
    suite_dirs: Option<Vec<String>>,
    /// Reference solver binary name for comparison (e.g., "z3").
    reference_solver: Option<String>,
    /// Competition-standard timeout declared by the eval registry.
    standard_timeout_sec: Option<f64>,
    /// CSV file with consensus results for HWMCC benchmarks.
    /// Format: benchmark,config,result,time_real,time_cpu,memory
    #[allow(dead_code)] // serde: deserialized from eval TOML but not yet loaded at runtime
    consensus_csv: Option<String>,
}

fn repo_root() -> PathBuf {
    repo_root_public()
}

/// Public wrapper: walk parents looking for the repo root (contains both
/// `Cargo.toml` and an `evals/` directory). Shared with the harvester module.
#[must_use]
pub fn repo_root_public() -> PathBuf {
    let mut dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    loop {
        if dir.join("Cargo.toml").exists() && dir.join("evals").exists() {
            return dir;
        }
        if !dir.pop() {
            return std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        }
    }
}

fn registry_dir() -> PathBuf {
    repo_root().join("evals").join("registry")
}

fn discover_evals() -> Result<Vec<(String, EvalSpec)>> {
    let dir = registry_dir();
    if !dir.exists() {
        return Err(BenchError::EvalRegistryMissing { path: dir });
    }

    let registry_paths = bounded_sorted_registry_paths(&dir)?;

    let mut evals = Vec::new();
    let mut seen_ids = BTreeMap::<String, PathBuf>::new();
    for path in registry_paths {
        if path.extension().and_then(|e| e.to_str()) != Some("yaml") {
            continue;
        }
        let text = crate::resource::read_bounded_text(
            &path,
            crate::resource::MAX_METADATA_BYTES,
            "eval registry entry",
        )?;
        let spec = parse_eval_spec_minimal(&text, &path)?;
        let eval_id = spec.id.clone().unwrap_or_else(|| {
            path.file_stem()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string()
        });
        validate_eval_id(&eval_id, &path)?;
        register_eval_id(&mut seen_ids, &eval_id, &path)?;
        evals.push((eval_id, spec));
    }
    evals.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(evals)
}

const MAX_EVAL_REGISTRY_ENTRIES: usize = 10_000;

fn bounded_sorted_registry_paths(dir: &Path) -> Result<Vec<PathBuf>> {
    bounded_sorted_registry_paths_with_limit(dir, MAX_EVAL_REGISTRY_ENTRIES)
}

fn bounded_sorted_registry_paths_with_limit(dir: &Path, limit: usize) -> Result<Vec<PathBuf>> {
    let mut paths = Vec::new();
    for entry in std::fs::read_dir(dir)? {
        if paths.len() >= limit {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "eval registry {} exceeds the {limit} directory-entry limit",
                    dir.display()
                ),
            });
        }
        paths.push(entry?.path());
    }
    paths.sort();
    Ok(paths)
}

fn register_eval_id(
    seen_ids: &mut BTreeMap<String, PathBuf>,
    eval_id: &str,
    path: &Path,
) -> Result<()> {
    if let Some(previous) = seen_ids.get(eval_id) {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "duplicate eval id {eval_id:?} in {} and {}",
                previous.display(),
                path.display()
            ),
        });
    }
    seen_ids.insert(eval_id.to_string(), path.to_path_buf());
    Ok(())
}

fn validate_eval_id(eval_id: &str, path: &Path) -> Result<()> {
    const MAX_EVAL_ID_BYTES: usize = 128;
    if eval_id.is_empty()
        || eval_id.len() > MAX_EVAL_ID_BYTES
        || matches!(eval_id, "." | "..")
        || !eval_id
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
    {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "eval id {eval_id:?} in {} must be a non-empty path-safe ASCII identifier of at most {MAX_EVAL_ID_BYTES} bytes",
                path.display()
            ),
        });
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EvalYamlSection {
    Other,
    Inputs,
}

const INPUT_KEYS: &[&str] = &[
    "timeout_sec",
    "benchmarks_dir",
    "list_file",
    "set_file",
    "runs",
    "suite_dirs",
    "reference_solver",
    "standard_timeout_sec",
    "consensus_csv",
];
const MAX_EVAL_SCALAR_BYTES: usize = 16 * 1024;
const MAX_EVAL_NUMERIC_BYTES: usize = 128;
const MAX_EVAL_SUITE_DIRS: usize = 10_000;

fn eval_yaml_error(path: &Path, line: usize, reason: impl std::fmt::Display) -> BenchError {
    BenchError::InvalidArgs {
        reason: format!(
            "invalid eval registry entry {}:{line}: {reason}",
            path.display()
        ),
    }
}

fn set_eval_string(
    slot: &mut Option<String>,
    raw: &str,
    key: &str,
    path: &Path,
    line: usize,
) -> Result<()> {
    if slot.is_some() {
        return Err(eval_yaml_error(
            path,
            line,
            format!("duplicate {key} field"),
        ));
    }
    let value = eval_string_value(raw, key, path, line)?;
    *slot = Some(value);
    Ok(())
}

fn eval_string_value(raw: &str, key: &str, path: &Path, line: usize) -> Result<String> {
    if raw.len() > MAX_EVAL_SCALAR_BYTES + 2 {
        return Err(eval_yaml_error(
            path,
            line,
            format!("{key} exceeds the {MAX_EVAL_SCALAR_BYTES} byte scalar limit"),
        ));
    }
    let quoted = matches!(
        yaml_value_without_comment(raw).as_bytes().first(),
        Some(b'"' | b'\'')
    );
    let value = parse_eval_string_scalar(raw, key, path, line)?;
    if value.is_empty()
        || value.len() > MAX_EVAL_SCALAR_BYTES
        || (!quoted
            && (matches!(value.as_str(), "~")
                || value.eq_ignore_ascii_case("null")
                || matches!(
                    value.as_bytes().first(),
                    Some(b'>' | b'|' | b'[' | b'{' | b'&' | b'*' | b'!' | b'@' | b'`')
                )))
    {
        return Err(eval_yaml_error(
            path,
            line,
            format!(
                "{key} must be a non-empty, well-formed scalar of at most {MAX_EVAL_SCALAR_BYTES} bytes"
            ),
        ));
    }
    Ok(value)
}

/// Parse the small YAML string-scalar subset supported by the eval registry.
///
/// Plain and single-quoted scalars are interpreted according to their YAML
/// spelling (including doubled single quotes). Double-quoted escape sequences
/// are rejected instead of being silently retained as backslash bytes: fully
/// decoding YAML's escape language belongs in a real YAML parser, and using a
/// differently interpreted solver/path value would be worse than rejecting the
/// registry entry.
fn parse_eval_string_scalar(raw: &str, key: &str, path: &Path, line: usize) -> Result<String> {
    let scalar = yaml_value_without_comment(raw);
    let Some(first) = scalar.as_bytes().first().copied() else {
        return Ok(String::new());
    };

    match first {
        b'"' => {
            let body = &scalar[1..];
            if body.contains('\\') {
                return Err(eval_yaml_error(
                    path,
                    line,
                    format!("{key} uses an unsupported double-quoted YAML escape"),
                ));
            }
            let Some(close) = body.find('"') else {
                return Err(eval_yaml_error(
                    path,
                    line,
                    format!("{key} has an unterminated double-quoted scalar"),
                ));
            };
            if !body[close + 1..].trim().is_empty() {
                return Err(eval_yaml_error(
                    path,
                    line,
                    format!("{key} has content after its quoted scalar"),
                ));
            }
            Ok(body[..close].to_string())
        }
        b'\'' => {
            let body = &scalar[1..];
            let bytes = body.as_bytes();
            let mut value = String::new();
            let mut segment_start = 0usize;
            let mut index = 0usize;
            while index < bytes.len() {
                if bytes[index] != b'\'' {
                    index += 1;
                    continue;
                }
                value.push_str(&body[segment_start..index]);
                if bytes.get(index + 1) == Some(&b'\'') {
                    value.push('\'');
                    index += 2;
                    segment_start = index;
                    continue;
                }
                if !body[index + 1..].trim().is_empty() {
                    return Err(eval_yaml_error(
                        path,
                        line,
                        format!("{key} has content after its quoted scalar"),
                    ));
                }
                return Ok(value);
            }
            Err(eval_yaml_error(
                path,
                line,
                format!("{key} has an unterminated single-quoted scalar"),
            ))
        }
        _ => Ok(scalar.to_string()),
    }
}

fn set_eval_positive_f64(
    slot: &mut Option<f64>,
    raw: &str,
    key: &str,
    path: &Path,
    line: usize,
) -> Result<()> {
    if slot.is_some() {
        return Err(eval_yaml_error(
            path,
            line,
            format!("duplicate {key} field"),
        ));
    }
    if raw.len() > MAX_EVAL_NUMERIC_BYTES {
        return Err(eval_yaml_error(
            path,
            line,
            format!("{key} numeric scalar is too long"),
        ));
    }
    let rendered = yaml_value_without_comment(raw);
    let value = rendered.parse::<f64>().map_err(|_| {
        eval_yaml_error(
            path,
            line,
            format!("{key} must be a finite positive number, got {rendered:?}"),
        )
    })?;
    if !value.is_finite() || value <= 0.0 {
        return Err(eval_yaml_error(
            path,
            line,
            format!("{key} must be a finite positive number, got {rendered:?}"),
        ));
    }
    *slot = Some(value);
    Ok(())
}

fn set_eval_positive_u32(
    slot: &mut Option<u32>,
    raw: &str,
    key: &str,
    path: &Path,
    line: usize,
) -> Result<()> {
    if slot.is_some() {
        return Err(eval_yaml_error(
            path,
            line,
            format!("duplicate {key} field"),
        ));
    }
    if raw.len() > MAX_EVAL_NUMERIC_BYTES {
        return Err(eval_yaml_error(
            path,
            line,
            format!("{key} numeric scalar is too long"),
        ));
    }
    let rendered = yaml_value_without_comment(raw);
    let value = rendered.parse::<u32>().map_err(|_| {
        eval_yaml_error(
            path,
            line,
            format!("{key} must be a positive integer, got {rendered:?}"),
        )
    })?;
    if value == 0 {
        return Err(eval_yaml_error(
            path,
            line,
            format!("{key} must be a positive integer"),
        ));
    }
    *slot = Some(value);
    Ok(())
}

/// Structurally parse the small, supported subset of the eval YAML registry.
///
/// Targeted fields are scope-aware and duplicate-rejecting. This deliberately
/// fails closed instead of letting a typo, malformed number, or same-named key
/// under another mapping silently select a default benchmark envelope.
fn parse_eval_spec_minimal(text: &str, path: &Path) -> Result<EvalSpec> {
    let mut id = None;
    let mut competition = None;
    let mut scoring = None;
    let mut timeout_sec = None;
    let mut benchmarks_dir = None;
    let mut list_file = None;
    let mut set_file = None;
    let mut runs = None;
    let mut reference_solver = None;
    let mut standard_timeout_sec = None;
    let mut consensus_csv = None;
    let mut suite_dirs: Option<Vec<String>> = None;
    let mut section = EvalYamlSection::Other;
    let mut inputs_seen = false;
    let mut input_field_indent = None;
    let mut suite_dirs_indent = None;

    for (zero_based_line, line) in text.lines().enumerate() {
        let line_number = zero_based_line + 1;
        if line.contains('\0') {
            return Err(eval_yaml_error(
                path,
                line_number,
                "NUL byte is not valid YAML text",
            ));
        }
        let content = line.trim_start_matches([' ', '\t']);
        let leading = &line[..line.len() - content.len()];
        if leading.contains('\t') {
            return Err(eval_yaml_error(
                path,
                line_number,
                "tab indentation is not supported",
            ));
        }
        let indent = leading.len();
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }

        if indent == 0 {
            section = EvalYamlSection::Other;
            input_field_indent = None;
            suite_dirs_indent = None;
            if matches!(trimmed, "---" | "...") {
                continue;
            }
            let (key, raw) = trimmed.split_once(':').ok_or_else(|| {
                eval_yaml_error(path, line_number, "expected a top-level YAML mapping field")
            })?;
            let key = key.trim();
            match key {
                "id" => set_eval_string(&mut id, raw, key, path, line_number)?,
                "competition" => {
                    set_eval_string(&mut competition, raw, key, path, line_number)?;
                }
                "scoring" => set_eval_string(&mut scoring, raw, key, path, line_number)?,
                "inputs" => {
                    if inputs_seen {
                        return Err(eval_yaml_error(
                            path,
                            line_number,
                            "duplicate inputs mapping",
                        ));
                    }
                    let value = yaml_value_without_comment(raw);
                    if !value.is_empty() {
                        return Err(eval_yaml_error(
                            path,
                            line_number,
                            "inputs must be a block YAML mapping",
                        ));
                    }
                    inputs_seen = true;
                    section = EvalYamlSection::Inputs;
                }
                key if INPUT_KEYS.contains(&key) => {
                    return Err(eval_yaml_error(
                        path,
                        line_number,
                        format!("{key} belongs under inputs"),
                    ));
                }
                _ => {}
            }
            continue;
        }

        if section != EvalYamlSection::Inputs {
            continue;
        }

        let direct_indent = *input_field_indent.get_or_insert(indent);
        if indent < direct_indent {
            return Err(eval_yaml_error(
                path,
                line_number,
                "inconsistent indentation inside inputs",
            ));
        }
        if indent > direct_indent {
            if suite_dirs_indent.is_some_and(|suite_indent| indent > suite_indent) {
                let item = trimmed.strip_prefix("- ").ok_or_else(|| {
                    eval_yaml_error(
                        path,
                        line_number,
                        "suite_dirs entries must be YAML list items",
                    )
                })?;
                let item = eval_string_value(item, "suite_dirs entry", path, line_number)?;
                let directories = suite_dirs.get_or_insert_with(Vec::new);
                if directories.len() >= MAX_EVAL_SUITE_DIRS {
                    return Err(eval_yaml_error(
                        path,
                        line_number,
                        format!("suite_dirs exceeds the {MAX_EVAL_SUITE_DIRS} entry limit"),
                    ));
                }
                directories.push(item);
                continue;
            }
            return Err(eval_yaml_error(
                path,
                line_number,
                "nested input content is supported only for suite_dirs",
            ));
        }

        suite_dirs_indent = None;
        let (key, raw) = trimmed.split_once(':').ok_or_else(|| {
            eval_yaml_error(path, line_number, "expected an inputs mapping field")
        })?;
        let key = key.trim();
        if matches!(key, "id" | "competition" | "scoring" | "inputs") {
            return Err(eval_yaml_error(
                path,
                line_number,
                format!("{key} is a top-level field"),
            ));
        }
        match key {
            "timeout_sec" => {
                set_eval_positive_f64(&mut timeout_sec, raw, key, path, line_number)?;
            }
            "benchmarks_dir" => {
                set_eval_string(&mut benchmarks_dir, raw, key, path, line_number)?;
            }
            "list_file" => set_eval_string(&mut list_file, raw, key, path, line_number)?,
            "set_file" => set_eval_string(&mut set_file, raw, key, path, line_number)?,
            "runs" => set_eval_positive_u32(&mut runs, raw, key, path, line_number)?,
            "reference_solver" => {
                set_eval_string(&mut reference_solver, raw, key, path, line_number)?;
            }
            "standard_timeout_sec" => {
                set_eval_positive_f64(&mut standard_timeout_sec, raw, key, path, line_number)?
            }
            "consensus_csv" => {
                set_eval_string(&mut consensus_csv, raw, key, path, line_number)?;
            }
            "suite_dirs" => {
                if suite_dirs.is_some() {
                    return Err(eval_yaml_error(
                        path,
                        line_number,
                        "duplicate suite_dirs field",
                    ));
                }
                let value = yaml_value_without_comment(raw);
                if value == "[]" {
                    suite_dirs = Some(Vec::new());
                } else if value.is_empty() {
                    suite_dirs = Some(Vec::new());
                    suite_dirs_indent = Some(indent);
                } else {
                    return Err(eval_yaml_error(
                        path,
                        line_number,
                        "suite_dirs must be a block list or []",
                    ));
                }
            }
            other => {
                return Err(eval_yaml_error(
                    path,
                    line_number,
                    format!("unsupported inputs field {other:?}"),
                ));
            }
        }
    }

    if !inputs_seen {
        return Err(eval_yaml_error(path, 1, "missing inputs mapping"));
    }

    let corpus_selector_count = [
        list_file.is_some(),
        set_file.is_some(),
        suite_dirs.is_some(),
    ]
    .into_iter()
    .filter(|selected| *selected)
    .count();
    if corpus_selector_count > 1 {
        return Err(eval_yaml_error(
            path,
            1,
            "list_file, set_file, and suite_dirs are mutually exclusive corpus selectors",
        ));
    }

    if id.is_none() {
        id = Some(
            path.file_stem()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string(),
        );
    }
    validate_eval_id(id.as_deref().unwrap_or_default(), path)?;

    Ok(EvalSpec {
        id,
        competition,
        scoring,
        inputs: Some(EvalInputs {
            timeout_sec,
            benchmarks_dir,
            list_file,
            set_file,
            runs,
            suite_dirs,
            reference_solver,
            standard_timeout_sec,
            consensus_csv,
        }),
    })
}

fn find_solver(name_or_path: &str) -> Option<PathBuf> {
    let requested = Path::new(name_or_path);
    if requested.is_absolute() || name_or_path.contains(std::path::MAIN_SEPARATOR) {
        return is_executable_file(requested).then(|| requested.to_path_buf());
    }
    let search_path = std::env::var_os("PATH")?;
    std::env::split_paths(&search_path).find_map(|directory| {
        let candidate = directory.join(name_or_path);
        is_executable_file(&candidate).then_some(candidate)
    })
}

fn resolve_configured_reference_solver(name_or_path: &str) -> Result<(String, PathBuf)> {
    let path = find_solver(name_or_path).ok_or_else(|| BenchError::SolverNotFound {
        name: name_or_path.to_string(),
    })?;
    Ok((crate::native::reference_display_name(&path), path))
}

fn is_executable_file(path: &Path) -> bool {
    let Ok(metadata) = std::fs::metadata(path) else {
        return false;
    };
    if !metadata.is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        if metadata.permissions().mode() & 0o111 == 0 {
            return false;
        }
    }
    true
}

/// Infer competition domain from eval ID prefix.
fn infer_domain(eval_id: &str) -> &str {
    if eval_id.starts_with("sat-") {
        "sat"
    } else if eval_id.starts_with("smt-") {
        "smt"
    } else if eval_id.starts_with("chccomp-") || eval_id.starts_with("chc-") {
        "chc"
    } else if eval_id.starts_with("hwmcc-") {
        "hwmcc"
    } else if eval_id.starts_with("sygus-") {
        "sygus"
    } else if eval_id.starts_with("maxsat-") {
        "maxsat"
    } else if eval_id.starts_with("qbf-") {
        "qbf"
    } else if eval_id.starts_with("allsat-") {
        "allsat"
    } else if eval_id.starts_with("counting-") {
        "counting"
    } else if eval_id.starts_with("omt-") {
        "omt"
    } else if eval_id.starts_with("security-") {
        if eval_id.contains("sygus") {
            "sygus"
        } else if eval_id.contains("omt") || eval_id.contains("maxsmt") {
            "omt"
        } else if eval_id.contains("qbf") || eval_id.contains("qdimacs") {
            "qbf"
        } else if eval_id.contains("allsat") || eval_id.contains("allsmt") {
            "allsat"
        } else if eval_id.contains("counting") || eval_id.contains("qif") {
            "counting"
        } else {
            // Default covers svcomp and anything else under `security-`.
            "smt"
        }
    } else {
        "unknown"
    }
}

fn infer_competition(eval_id: &str) -> Competition {
    match infer_domain(eval_id) {
        "sat" => Competition::SatComp,
        "smt" => Competition::SmtComp,
        "chc" => Competition::ChcComp,
        "hwmcc" => Competition::HwmccComp,
        "sygus" | "maxsat" | "qbf" | "allsat" | "counting" | "omt" => Competition::ChcComp,
        _ => Competition::SmtComp,
    }
}

fn infer_division(eval_id: &str) -> String {
    if let Some(suffix) = eval_id.strip_prefix("smt-smtcomp-") {
        suffix.to_uppercase().replace('-', "_")
    } else if let Some(suffix) = eval_id.strip_prefix("smt-local-") {
        if suffix == "suite" {
            "mixed".to_string()
        } else {
            suffix.to_uppercase().replace('-', "_")
        }
    } else {
        "unknown".to_string()
    }
}

fn infer_track(eval_id: &str) -> String {
    if eval_id.contains("extra-small-lia") {
        "LIA-extra-small".to_string()
    } else if eval_id.contains("lia-lin") {
        "LIA-Lin".to_string()
    } else if eval_id.contains("lia") {
        "LIA".to_string()
    } else {
        "unknown".to_string()
    }
}

fn infer_hwmcc_track(eval_id: &str) -> String {
    if eval_id.contains("wordlevel-bv") {
        "wordlevel-bv".to_string()
    } else if eval_id.contains("wordlevel-array") {
        "wordlevel-array".to_string()
    } else if eval_id.contains("bitlevel") {
        "bitlevel".to_string()
    } else {
        "unknown".to_string()
    }
}

fn inferred_scoring_label(eval_id: &str) -> &'static str {
    match infer_competition(eval_id) {
        Competition::SatComp => "sat-comp",
        Competition::SmtComp => "smt-comp",
        Competition::ChcComp => "chc-comp",
        Competition::HwmccComp => "hwmcc",
    }
}

fn scoring_label(eval_id: &str, spec: &EvalSpec) -> String {
    spec.scoring
        .as_deref()
        .or(spec.competition.as_deref())
        .map(ToOwned::to_owned)
        .unwrap_or_else(|| inferred_scoring_label(eval_id).to_string())
}

fn standard_timeout_sec(eval_id: &str, spec: &EvalSpec) -> f64 {
    spec.inputs
        .as_ref()
        .and_then(|i| i.standard_timeout_sec)
        .unwrap_or_else(|| infer_competition(eval_id).standard_timeout())
}

fn competition_timeout(eval_id: &str) -> f64 {
    infer_competition(eval_id).standard_timeout()
}

// ===================================================================
// Eval execution
// ===================================================================

pub struct RunArgs {
    pub eval_ids: Vec<String>,
    pub all: bool,
    pub domain: Option<String>,
    pub competition: bool,
    pub ay: PathBuf,
    pub timeout: Option<f64>,
    pub output: Option<PathBuf>,
    /// CLI override for number of runs per benchmark.
    /// `None` means use the YAML registry value, then fall back to 1.
    pub runs: Option<u32>,
    /// Zero-based deterministic shard cursor. Must be paired with
    /// `shard_size`; stale cursors are normalized after corpus preflight.
    pub shard_index: Option<usize>,
    /// Maximum number of benchmarks selected for this invocation.
    pub shard_size: Option<usize>,
    /// CLI override for reference solvers as (name, path) pairs, in the
    /// order given on the command line. Empty means fall back to the YAML
    /// spec's single `reference_solver` name.
    pub reference_solvers: Vec<(String, PathBuf)>,
    /// Comparison run class ("replay" | "laptop") stamped into results.json
    /// with a host fingerprint. Never verified here — `bench compare` owns
    /// verification; a class stamped this way is recorded as unverified.
    pub run_class: Option<String>,
    pub quiet: bool,
    /// When `true`, compute proof-complexity features for each input
    /// file and persist them alongside the solver result (#8774).
    pub with_features: bool,
    /// SAT-COMP track metadata recorded in results for profile-correct SAT runs.
    pub sat_track: Option<String>,
    /// SAT-COMP AI-class metadata recorded in results for profile-correct SAT runs.
    pub sat_ai_class: Option<String>,
    /// SAT solver variant passed to ay as `--sat-variant` for SAT runs.
    pub sat_variant: Option<String>,
}

/// Score an existing results file and print the result.
fn score_and_print(
    results_path: &Path,
    eval_id: &str,
    timeout: f64,
    competition_mode: bool,
) -> Result<serde_json::Value> {
    let data = ResultsFile::load(results_path)?;
    let items = data.items();
    let mode = if competition_mode {
        "competition"
    } else {
        "dev"
    };
    let comp = infer_competition(eval_id);

    match comp {
        Competition::SatComp => {
            let score = scoring::score_sat(items, timeout);
            println!("  [{mode}, T={timeout:.0}s] {score}");
            Ok(serde_json::to_value(&score)?)
        }
        Competition::SmtComp => {
            let div = infer_division(eval_id);
            let score = scoring::score_smt(items, timeout, &div);
            println!("  [{mode}, T={timeout:.0}s] {score}");
            Ok(serde_json::to_value(&score)?)
        }
        Competition::ChcComp => {
            let track = infer_track(eval_id);
            let score = scoring::score_chc(items, timeout, &track);
            println!("  [{mode}, T={timeout:.0}s] {score}");
            Ok(serde_json::to_value(&score)?)
        }
        Competition::HwmccComp => {
            let track = infer_hwmcc_track(eval_id);
            let score = scoring::score_hwmcc(items, timeout, &track);
            println!("  [{mode}, T={timeout:.0}s] {score}");
            Ok(serde_json::to_value(&score)?)
        }
    }
}

fn run_single_eval(
    eval_id: &str,
    spec: &EvalSpec,
    args: &RunArgs,
    resources: &crate::resource::PlannedResources,
    ay_path: &Path,
    pinned_ay: &crate::environment::PinnedSolver,
    environment: &crate::environment::Environment,
) -> Result<(serde_json::Value, Option<serde_json::Value>)> {
    let inputs = spec.inputs.as_ref();

    // Determine timeout
    let timeout = if let Some(t) = args.timeout {
        t
    } else if args.competition {
        competition_timeout(eval_id)
    } else {
        inputs.and_then(|i| i.timeout_sec).unwrap_or(60.0)
    };
    if !timeout.is_finite() || timeout <= 0.0 {
        return Err(BenchError::InvalidArgs {
            reason: format!("timeout for eval {eval_id} must be finite and positive"),
        });
    }

    let mode_label = if args.competition {
        "COMPETITION"
    } else {
        "dev"
    };

    if !args.quiet {
        eprintln!();
        eprintln!("{}", "=".repeat(60));
        eprintln!("[{eval_id}] mode={mode_label} timeout={timeout:.0}s");
        eprintln!("{}", "=".repeat(60));
    }

    let root = repo_root();
    let domain = infer_domain(eval_id);
    // Native eval execution is intentionally sequential, but the job-1 case
    // still needs an explicit envelope: the main ay binary otherwise claims
    // 85% of machine RAM.  Keep `_oom_guard.py` as the admission-policy source
    // and persist its exact plan in results.json.
    if !args.quiet {
        eprintln!(
            "[resource] jobs={} --memory={} MiB NBCORE={} headroom={} MiB",
            resources.plan.jobs,
            resources.plan.memlimit_mb_per_child,
            resources.plan.nbcore_per_child,
            resources.plan.headroom_mb,
        );
    }

    // Determine benchmarks_dir from spec or infer from domain
    let benchmarks_dir = spec
        .inputs
        .as_ref()
        .and_then(|i| i.benchmarks_dir.as_deref())
        .map(|d| expand_tilde(d, &root))
        .unwrap_or_else(|| root.join("benchmarks").join(domain));

    // Build explicit file list from list_file, set_file, or suite_dirs
    let file_list = match build_file_list(spec, &root, &benchmarks_dir)? {
        Some(file_list) => Some(file_list),
        None => build_suite_dirs_list(spec, &benchmarks_dir, domain)?,
    };

    let runs = effective_runs(args, inputs)?;

    // Resolve reference solvers: CLI --reference-solver values override the
    // YAML spec's single reference_solver name.
    let reference_solvers: Vec<(String, PathBuf)> = if args.reference_solvers.is_empty() {
        match inputs.and_then(|i| i.reference_solver.as_deref()) {
            Some(reference_solver) => {
                vec![resolve_configured_reference_solver(reference_solver)?]
            }
            None => Vec::new(),
        }
    } else {
        args.reference_solvers.clone()
    };

    let run_id = environment.timestamp.replace(':', "-");
    let eval_output_root = bench_results_root(&root).join(eval_id);
    std::fs::create_dir_all(&eval_output_root)?;
    let run_dir = tempfile::Builder::new()
        .prefix(&format!("{run_id}-"))
        .tempdir_in(&eval_output_root)
        .with_bench_context(|| format!("reserving unique run directory for {eval_id}"))?;
    let output_dir = run_dir.path().to_path_buf();
    let artifact_output_dir = if domain == "sat" {
        Some(output_dir.join("artifacts"))
    } else {
        None
    };

    // Native execution owns the authoritative --memory flag. Passing it via
    // solver_args would either duplicate or override the admitted envelope.
    let solver_args = solver_args_for_eval(domain, args);
    let native_args = crate::native::NativeRunArgs {
        ay: ay_path,
        benchmarks_dir: &benchmarks_dir,
        timeout_sec: timeout,
        domain,
        quiet: args.quiet,
        with_features: args.with_features,
        file_list,
        shard: shard_selection(args)?,
        runs,
        reference_solvers,
        run_class: args.run_class.clone(),
        solver_args,
        sat_track: args.sat_track.clone(),
        sat_ai_class: args.sat_ai_class.clone(),
        sat_variant: args.sat_variant.clone(),
        environment: Some(environment.clone()),
        pinned_ay: Some(pinned_ay),
        artifact_output_dir,
        resources: Some(resources.clone()),
    };

    let results = crate::native::run_native(&native_args)?;
    let shard = results
        .settings
        .shard
        .as_ref()
        .map(serde_json::to_value)
        .transpose()?;

    // Print comparison summaries if reference solvers were used
    if let Some(references) = results.references.as_deref() {
        if !args.quiet {
            for summary in references {
                eprintln!();
                eprintln!(
                    "[{eval_id}] comparison vs {} {} ({})",
                    summary.reference_solver,
                    summary.reference_solver_build_stamp,
                    summary.reference_solver_path,
                );
                eprintln!(
                    "  agree={} disagree={} ay_only={} ref_only={}",
                    summary.agree, summary.disagree, summary.ay_only, summary.ref_only,
                );
                if summary.both_solved > 0 {
                    eprintln!(
                        "  both_solved={}: ay_faster={} ref_faster={} ay_total={:.1}s ref_total={:.1}s",
                        summary.both_solved,
                        summary.ay_faster,
                        summary.ref_faster,
                        summary.ay_total_time,
                        summary.ref_total_time,
                    );
                }
            }
        }
    }

    let results_path = output_dir.join("results.json");
    let json = serde_json::to_string_pretty(&results)?;
    atomic_write_new(&results_path, json.as_bytes())?;

    if !args.quiet {
        eprintln!("[{eval_id}] results written to {}", results_path.display());
    }

    // Score before publication. Any failure drops the TempDir and removes
    // partial evidence; a successful run keeps its already-unique directory.
    let score = score_and_print(&results_path, eval_id, timeout, args.competition)?;
    let partial_shard = results.settings.shard.as_ref().is_some_and(|metadata| {
        metadata.selected_benchmark_count < metadata.corpus_benchmark_count
    });
    // Persist only complete evals in the comparable result store. A partial
    // shard is independently scoreable evidence, but the current store key has
    // no campaign/shard identity; inserting it would manufacture misleading
    // added/removed diffs and mix repeated shards from one commit.
    if !partial_shard {
        if let Err(e) = persist_results(&root, eval_id, &results, args.with_features) {
            eprintln!("[{eval_id}] warning: failed to persist results to store: {e:#}");
        }
    } else if !args.quiet {
        eprintln!(
            "[{eval_id}] partial shard evidence is not inserted into the comparable result store"
        );
    }
    let published_dir = run_dir.keep();
    if !args.quiet {
        eprintln!(
            "[{eval_id}] run directory published at {}",
            published_dir.display()
        );
    }
    Ok((score, shard))
}

fn bench_results_root(repo_root: &Path) -> PathBuf {
    resolve_results_root(
        repo_root,
        std::env::var_os("AY_BENCH_RESULTS_ROOT").map(PathBuf::from),
    )
}

fn resolve_results_root(repo_root: &Path, configured: Option<PathBuf>) -> PathBuf {
    let Some(path) = configured.filter(|path| !path.as_os_str().is_empty()) else {
        return repo_root.join("evals").join("results");
    };
    if path.is_absolute() {
        path
    } else {
        repo_root.join(path)
    }
}

fn atomic_write_new(path: &Path, contents: &[u8]) -> Result<()> {
    let resolved = resolve_publication_target(path)?;
    let parent = resolved.parent().ok_or_else(|| BenchError::InvalidArgs {
        reason: format!("output path has no parent: {}", resolved.display()),
    })?;
    let mut temporary = tempfile::NamedTempFile::new_in(parent)?;
    temporary.write_all(contents)?;
    temporary.as_file().sync_all()?;
    temporary
        .persist_noclobber(&resolved)
        .map_err(|error| error.error)
        .with_bench_context(|| format!("publishing {}", resolved.display()))?;
    sync_publication_directory(parent)?;
    Ok(())
}

fn atomic_write_replace(path: &Path, contents: &[u8]) -> Result<()> {
    let resolved = resolve_publication_target(path)?;
    let parent = resolved.parent().ok_or_else(|| BenchError::InvalidArgs {
        reason: format!("output path has no parent: {}", resolved.display()),
    })?;
    let mut temporary = tempfile::NamedTempFile::new_in(parent)?;
    temporary.write_all(contents)?;
    temporary.as_file().sync_all()?;
    temporary
        .persist(&resolved)
        .map_err(|error| error.error)
        .with_bench_context(|| format!("publishing {}", resolved.display()))?;
    sync_publication_directory(parent)?;
    Ok(())
}

fn sync_publication_directory(parent: &Path) -> Result<()> {
    #[cfg(unix)]
    {
        std::fs::File::open(parent)?.sync_all()?;
    }
    #[cfg(not(unix))]
    let _ = parent;
    Ok(())
}

fn resolve_publication_target(path: &Path) -> Result<PathBuf> {
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let file_name = path.file_name().ok_or_else(|| BenchError::InvalidArgs {
        reason: format!("output path has no file name: {}", path.display()),
    })?;
    std::fs::create_dir_all(parent)?;
    let canonical_parent = std::fs::canonicalize(parent)
        .with_bench_context(|| format!("resolving output directory {}", parent.display()))?;
    if !canonical_parent.is_dir() {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "output parent is not a directory: {}",
                canonical_parent.display()
            ),
        });
    }
    Ok(canonical_parent.join(file_name))
}

fn effective_runs(args: &RunArgs, inputs: Option<&EvalInputs>) -> Result<u32> {
    let runs = args
        .runs
        .or_else(|| inputs.and_then(|i| i.runs))
        .unwrap_or(1);
    if runs == 0 {
        return Err(BenchError::InvalidArgs {
            reason: "runs must be at least 1".to_string(),
        });
    }
    Ok(runs)
}

fn shard_selection(args: &RunArgs) -> Result<Option<crate::native::NativeShardSelection>> {
    match (args.shard_index, args.shard_size) {
        (None, None) => Ok(None),
        (Some(index), Some(size)) if (1..=crate::native::MAX_NATIVE_SHARD_SIZE).contains(&size) => {
            Ok(Some(crate::native::NativeShardSelection { index, size }))
        }
        (Some(_), Some(size)) => Err(BenchError::InvalidArgs {
            reason: format!(
                "shard_size must be in 1..={}, got {size}",
                crate::native::MAX_NATIVE_SHARD_SIZE
            ),
        }),
        _ => Err(BenchError::InvalidArgs {
            reason: "shard_index and shard_size must be provided together".to_string(),
        }),
    }
}

fn solver_args_for_eval(domain: &str, args: &RunArgs) -> Vec<String> {
    let mut solver_args = Vec::new();
    if domain == "sat" {
        if let Some(variant) = args.sat_variant.as_deref() {
            solver_args.push("--sat-variant".to_string());
            solver_args.push(variant.to_string());
        }
    }
    solver_args
}

/// Persist a completed eval's per-benchmark rows into the sqlite store at
/// `.ay-bench/results.sqlite` under `repo_root`, keyed by the current git HEAD.
///
/// Publication is allowed only for a full, clean commit captured before the
/// campaign and revalidated immediately before the transaction. This prevents
/// a dirty tree or concurrent checkout from colliding with comparable rows.
fn persist_results(
    repo_root: &Path,
    eval_id: &str,
    results: &crate::native::NativeResults,
    with_features: bool,
) -> Result<()> {
    let commit_hash = results.environment.git_commit.as_str();
    if !results.environment.comparable_git_state
        || !crate::environment::valid_full_commit(commit_hash)
        || results.environment.git_dirty != Some(false)
    {
        return Err(BenchError::msg(format!(
            "{eval_id}: refusing comparable-store publication from a dirty, unknown, or non-full captured git state"
        )));
    }
    let (current_commit, current_dirty) = crate::environment::Environment::git_state(repo_root);
    if current_commit != commit_hash || current_dirty != Some(false) {
        return Err(BenchError::msg(format!(
            "{eval_id}: repository HEAD or cleanliness changed during the benchmark campaign; refusing publication"
        )));
    }

    let store_path = StorePath::configured_at(repo_root);
    let mut store = ResultsStore::open(store_path.as_path())?;
    let rows = build_rows(commit_hash, eval_id, results, with_features)?;
    store.upsert_rows(&rows)?;
    Ok(())
}

/// Build `ResultRow`s from a completed `NativeResults`. Each row encodes the
/// per-benchmark verdict plus a three-valued `verifier_ok` flag:
///
/// * `1` if the comparison block declares the result "agree" with the
///   reference solver, OR if the parsed verdict matches the `expected` label
///   embedded in the path.
/// * `0` if the comparison says "disagree" (i.e. wrong answer).
/// * `-1` when there was no comparison and no expected label — verdict is
///   taken at face value.
fn build_rows(
    commit_hash: &str,
    eval_id: &str,
    results: &crate::native::NativeResults,
    with_features: bool,
) -> Result<Vec<ResultRow>> {
    // Index comparison items (if present) by file path so we can look up
    // agreement quickly.
    let mut comp_index: BTreeMap<&str, Vec<&'static str>> = BTreeMap::new();
    if let Some(reference_comparisons) = results.reference_comparisons.as_deref() {
        for reference in reference_comparisons {
            for comparison in &reference.items {
                comp_index
                    .entry(comparison.file.as_str())
                    .or_default()
                    .push(comparison.agreement);
            }
        }
    } else {
        // Backward compatibility for in-memory/legacy results that only carry
        // the first reference's rows.
        for comparison in results.comparisons.as_deref().unwrap_or(&[]) {
            comp_index
                .entry(comparison.file.as_str())
                .or_default()
                .push(comparison.agreement);
        }
    }

    let timestamp = results.environment.timestamp.clone();
    let resource_plan = results
        .settings
        .resource_plan
        .as_ref()
        .ok_or_else(|| BenchError::msg("native results are missing their resource plan"))?;
    let resource_enforcement = results
        .settings
        .resource_enforcement
        .as_deref()
        .ok_or_else(|| BenchError::msg("native results are missing exact resource enforcement"))?;
    let resource_envelope = Some(crate::resource::effective_execution_envelope(
        resource_plan,
        resource_enforcement,
        results.settings.timeout_sec,
    )?);

    results
        .items
        .iter()
        .map(|item| -> Result<ResultRow> {
            let verifier_ok = classify_verifier(item, &comp_index);
            let runtime = std::time::Duration::try_from_secs_f64(item.time_sec).map_err(|_| {
                BenchError::msg(format!(
                    "{eval_id}: invalid runtime evidence for {}: {:?}",
                    item.benchmark_path, item.time_sec
                ))
            })?;
            let runtime_ms = i64::try_from(runtime.as_millis()).map_err(|_| {
                BenchError::msg(format!(
                    "{eval_id}: runtime evidence exceeds persistent-store range for {}",
                    item.benchmark_path
                ))
            })?;
            let extracted = if with_features {
                Some(item.extracted_features.clone().ok_or_else(|| {
                    BenchError::msg(format!(
                        "{eval_id}: requested feature evidence is missing for private solver input {}",
                        item.benchmark_path
                    ))
                })?)
            } else {
                None
            };
            let (family, fmax, fmean, xor, card, modu, fms) = match extracted {
                Some(ef) => (
                    ef.family,
                    Some(i64::from(ef.features.clause_width_max)),
                    Some(ef.features.clause_width_mean),
                    Some(ef.features.xor_density),
                    Some(ef.features.cardinality_density),
                    Some(ef.features.modularity),
                    Some(ef.extract_ms),
                ),
                None => (None, None, None, None, None, None, None),
            };
            let artifacts = item.artifacts.as_ref();
            let artifact_output_dir = artifacts.map(|artifacts| artifacts.output_dir.clone());
            let proof_path = artifacts.and_then(|artifacts| artifacts.proof_path.clone());
            let proof_format = artifacts.and_then(|artifacts| artifacts.proof_format.clone());
            let proof_exists = artifacts.and_then(|artifacts| artifacts.proof_exists);
            let proof_bytes = artifacts
                .and_then(|artifacts| artifacts.proof_bytes)
                .map(i64::try_from)
                .transpose()
                .map_err(|_| {
                    BenchError::msg(format!(
                        "{eval_id}: proof size exceeds persistent-store range for {}",
                        item.benchmark_path
                    ))
                })?;
            let proof_hash = artifacts.and_then(|artifacts| artifacts.proof_hash.clone());
            let proof_validation = artifacts.map(|artifacts| artifacts.proof_validation.clone());
            Ok(ResultRow {
                commit_hash: commit_hash.to_string(),
                eval_name: eval_id.to_string(),
                benchmark_path: item.benchmark_path.clone(),
                result: item.result.clone(),
                runtime_ms,
                // NativeResultItem does not currently capture per-benchmark
                // peak RSS; leave the column as zero until we add that.
                memory_mb: 0,
                verifier_ok,
                timestamp: timestamp.clone(),
                resource_envelope: resource_envelope.clone(),
                benchmark_content_hash: item.benchmark_content_hash.clone(),
                artifact_output_dir,
                proof_path,
                proof_format,
                proof_exists,
                proof_bytes,
                proof_hash,
                proof_validation,
                family,
                clause_width_max: fmax,
                clause_width_mean: fmean,
                xor_density: xor,
                cardinality_density: card,
                modularity: modu,
                feature_extract_ms: fms,
            })
        })
        .collect()
}

/// Classify a `NativeResultItem` against the comparison index and expected
/// label to produce `verifier_ok` (-1 / 0 / 1).
fn classify_verifier(
    item: &crate::native::NativeResultItem,
    comp_index: &BTreeMap<&str, Vec<&'static str>>,
) -> i32 {
    if let Some(agreements) = comp_index.get(item.file.as_str()) {
        // Any definite contradictory reference invalidates the result. A
        // first-reference agreement must never hide a later disagreement.
        if agreements.contains(&"disagree") {
            return 0;
        }
        if agreements.contains(&"agree") {
            return 1;
        }
        // ay_only / ref_only mean one side timed out — not a wrong answer, but
        // also not verified. Continue to an expected-label check if available.
    }
    // No comparison available. Fall back to `expected` label (when present).
    let authoritative_expected = matches!(
        item.expected_source.as_str(),
        "header" | "path" | "header+path"
    );
    if authoritative_expected {
        if let Some(expected) = item.expected.as_deref() {
            let got = item.result.to_ascii_lowercase();
            let exp = expected.to_ascii_lowercase();
            if got == exp {
                return 1;
            }
            // Only call it wrong if the solver claimed a verdict.
            if got == "sat" || got == "unsat" {
                return 0;
            }
        }
    }
    -1
}

pub fn cmd_run(args: RunArgs) -> Result<()> {
    validate_run_class(args.run_class.as_deref())?;
    shard_selection(&args)?;
    let evals = discover_evals()?;
    if evals.is_empty() {
        return Err(BenchError::msg("no eval specs found in evals/registry/"));
    }

    // Determine which evals to run
    let selected = select_evals_for_run(evals, &args)?;

    if selected.is_empty() {
        return Err(BenchError::msg("no matching evals found"));
    }
    // Validate every selected campaign before starting any of them. In
    // particular, `--all` must not publish a partial scorecard and only then
    // discover that a registry domain has no sound invocation/scoring path.
    for (eval_id, _) in &selected {
        crate::native::validate_native_domain(infer_domain(eval_id)).map_err(|error| {
            BenchError::InvalidArgs {
                reason: format!("eval {eval_id}: {error}"),
            }
        })?;
    }

    // Check AY binary
    let ay_path = if args.ay.is_relative() {
        repo_root().join(&args.ay)
    } else {
        args.ay.clone()
    };
    if !is_executable_file(&ay_path) {
        return Err(BenchError::msg(format!(
            "AY binary is missing, not a regular file, or not executable: {}\nBuild first: cargo build --release -p ay",
            ay_path.display()
        )));
    }
    // Selected evals execute sequentially, so one job-1 admission plan is the
    // effective envelope for the complete command and its scorecard probe.
    let root = repo_root();
    let resources = crate::resource::PlannedResources::plan(&root, 1, "ay bench run")?;
    let pinned_ay = crate::environment::PinnedSolver::capture(
        &ay_path,
        &resources,
        "ay bench pinned AY version probe",
    )?;
    let environment = crate::environment::Environment::capture_with_solver_in_repo(
        pinned_ay.provenance().clone(),
        &root,
    );

    let mut all_scores = Vec::new();
    let mut failures = Vec::new();

    for (eval_id, spec) in &selected {
        match run_single_eval(
            eval_id,
            spec,
            &args,
            &resources,
            &ay_path,
            &pinned_ay,
            &environment,
        ) {
            Ok((score, shard)) => {
                let mut row = serde_json::json!({
                    "eval_id": eval_id,
                    "competition": infer_competition(eval_id).name(),
                    "score": score,
                });
                if let Some(shard) = shard {
                    row["shard"] = shard;
                }
                all_scores.push(row);
            }
            Err(e) => {
                eprintln!("[{eval_id}] error: {e:#}");
                failures.push(format!("{eval_id}: {e:#}"));
                all_scores.push(serde_json::json!({
                    "eval_id": eval_id,
                    "error": format!("{e:#}"),
                }));
            }
        }
    }

    // Print scorecard
    let mode = if args.competition {
        "competition-standard timeouts"
    } else {
        "dev timeouts"
    };
    println!();
    println!("{}", "=".repeat(60));
    println!("SCORECARD ({mode})");
    println!("{}", "=".repeat(60));
    println!("Scores printed above per eval.");

    // Write combined output
    pinned_ay.verify_source()?;
    if let Some(ref output_path) = args.output {
        let scorecard = serde_json::json!({
            "environment": environment,
            "mode": if args.competition { "competition" } else { "dev" },
            "results": all_scores,
        });
        let scorecard_json = serde_json::to_string_pretty(&scorecard)?;
        atomic_write_replace(output_path, scorecard_json.as_bytes())?;
        println!("Scorecard written to: {}", output_path.display());
    }

    if failures.is_empty() {
        Ok(())
    } else {
        Err(BenchError::msg(format!(
            "{} eval(s) failed: {}",
            failures.len(),
            failures.join("; ")
        )))
    }
}

fn validate_run_class(run_class: Option<&str>) -> Result<()> {
    match run_class {
        None | Some("replay" | "laptop") => Ok(()),
        Some(other) => Err(BenchError::InvalidArgs {
            reason: format!("run_class must be 'replay' or 'laptop', got {other:?}"),
        }),
    }
}

fn select_evals_for_run(
    evals: Vec<(String, EvalSpec)>,
    args: &RunArgs,
) -> Result<Vec<(String, EvalSpec)>> {
    let selected: Vec<(String, EvalSpec)> = if args.all {
        evals
    } else if let Some(ref domain) = args.domain {
        evals
            .into_iter()
            .filter(|(id, _)| infer_domain(id) == domain.as_str())
            .collect()
    } else if !args.eval_ids.is_empty() {
        let available: Vec<String> = evals.iter().map(|(id, _)| id.clone()).collect();
        let unknown: Vec<String> = args
            .eval_ids
            .iter()
            .filter(|id| !available.contains(id))
            .cloned()
            .collect();
        if !unknown.is_empty() {
            return Err(BenchError::EvalNotFound {
                ids: format!(
                    "{}\navailable: {}",
                    unknown.join(", "),
                    available.join(", ")
                ),
            });
        }
        evals
            .into_iter()
            .filter(|(id, _)| args.eval_ids.contains(id))
            .collect()
    } else {
        return Err(BenchError::InvalidArgs {
            reason: "specify eval IDs, --all, or --domain {sat,smt,chc}".to_string(),
        });
    };

    Ok(selected)
}

// ===================================================================
// diff command
// ===================================================================

/// Output format for `ay-bench diff`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiffFormat {
    Table,
    Json,
    /// GitHub-flavored-markdown; suitable for PR comments.
    Markdown,
}

/// Arguments for `ay-bench diff`.
pub struct DiffArgs {
    pub base: String,
    pub head: String,
    pub eval: Option<String>,
    pub format: DiffFormat,
    /// Slowdown threshold in percent (default 20.0).
    pub slowdown_threshold_pct: f64,
}

impl Default for DiffArgs {
    fn default() -> Self {
        Self {
            base: "HEAD~10".to_string(),
            head: "HEAD".to_string(),
            eval: None,
            format: DiffFormat::Table,
            slowdown_threshold_pct: 20.0,
        }
    }
}

/// Run the `ay-bench diff` subcommand. Returns `true` iff regressions or
/// non-comparable resource envelopes were detected (the CLI layer maps that
/// to a non-zero exit code rather than silently accepting an invalid diff).
pub fn cmd_diff(args: DiffArgs) -> Result<bool> {
    let root = repo_root();

    // Resolve base / head to commit hashes. Fall back to the raw input so
    // users can pass explicit SHAs for commits that may not be present in
    // the worktree (e.g. imported from another machine).
    let base_hash = crate::db::resolve_rev(&root, &args.base).unwrap_or_else(|| args.base.clone());
    let head_hash = crate::db::resolve_rev(&root, &args.head).unwrap_or_else(|| args.head.clone());

    let store_path = StorePath::configured_at(&root);
    if !store_path.as_path().exists() {
        return Err(BenchError::msg(format!(
            "no persistent results store at {} — run `ay-bench run <eval>` first",
            store_path.as_path().display()
        )));
    }
    let store = ResultsStore::open(store_path.as_path())?;

    let opts = crate::diff::DiffOptions {
        slowdown_threshold_pct: args.slowdown_threshold_pct,
    };
    let report =
        crate::diff::diff_from_store(&store, &base_hash, &head_hash, args.eval.as_deref(), opts)?;

    match args.format {
        DiffFormat::Table => {
            print!("{}", crate::diff::render_table(&report));
        }
        DiffFormat::Json => {
            println!("{}", crate::diff::render_json(&report)?);
        }
        DiffFormat::Markdown => {
            print!("{}", crate::diff::render_markdown(&report));
        }
    }

    Ok(report.has_regressions() || report.has_non_comparable())
}

// ===================================================================
// list command
// ===================================================================

pub fn cmd_list() -> Result<()> {
    let evals = discover_evals()?;
    if evals.is_empty() {
        println!("No evals found in evals/registry/");
        return Ok(());
    }

    println!(
        "{:<40} {:<8} {:<12} {:<10} {:<12}",
        "Eval ID", "Domain", "Scoring", "Timeout", "Std Timeout"
    );
    println!("{}", "-".repeat(90));

    for row in eval_list_rows(&evals) {
        println!(
            "{:<40} {:<8} {:<12} {:<10} {:<12}",
            row.eval_id, row.domain, row.scoring, row.dev_timeout, row.standard_timeout,
        );
    }

    Ok(())
}

#[derive(Debug, PartialEq, Eq)]
struct EvalListRow {
    eval_id: String,
    domain: String,
    scoring: String,
    dev_timeout: String,
    standard_timeout: String,
}

fn eval_list_rows(evals: &[(String, EvalSpec)]) -> Vec<EvalListRow> {
    evals
        .iter()
        .map(|(eval_id, spec)| {
            let dev_timeout = spec
                .inputs
                .as_ref()
                .and_then(|i| i.timeout_sec)
                .map(|t| format!("{t:.0}s"))
                .unwrap_or_else(|| "?".to_string());
            EvalListRow {
                eval_id: eval_id.clone(),
                domain: infer_domain(eval_id).to_string(),
                scoring: scoring_label(eval_id, spec),
                dev_timeout,
                standard_timeout: format!("{:.0}s", standard_timeout_sec(eval_id, spec)),
            }
        })
        .collect()
}

// ===================================================================
// Helpers
// ===================================================================

/// Build an explicit benchmark file list from list_file or set_file.
///
/// - `list_file`: text file with one path per line (relative to repo root).
///   Lines starting with `#` or empty are skipped. Optional second column
///   is ignored (used for expected result in some formats).
/// - `set_file`: manifest relative to benchmarks_dir, listing paths relative
///   to benchmarks_dir. Lines ending in `.yml` are converted to `.smt2`.
///
/// Returns `None` if neither is specified (caller uses directory discovery).
const MAX_MANIFEST_BENCHMARKS: usize = 1_000_000;
const MAX_MISSING_PATH_EXAMPLES: usize = 8;

fn build_file_list(
    spec: &EvalSpec,
    root: &Path,
    benchmarks_dir: &Path,
) -> Result<Option<Vec<PathBuf>>> {
    let inputs = match spec.inputs.as_ref() {
        Some(i) => i,
        None => return Ok(None),
    };

    if let Some(ref list_path) = inputs.list_file {
        let path = root.join(list_path);
        let text = crate::resource::read_bounded_text(
            &path,
            crate::resource::MAX_METADATA_BYTES,
            "benchmark list file",
        )?;
        let mut files = Vec::new();
        let mut total = 0usize;
        let mut missing_count = 0usize;
        let mut missing_examples = Vec::new();
        for line in text.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            total = total
                .checked_add(1)
                .ok_or_else(|| BenchError::InvalidArgs {
                    reason: format!("list_file {list_path} contains too many entries"),
                })?;
            if total > MAX_MANIFEST_BENCHMARKS {
                return Err(BenchError::InvalidArgs {
                    reason: format!(
                        "list_file {list_path} exceeds the {MAX_MANIFEST_BENCHMARKS} benchmark limit"
                    ),
                });
            }
            // First column is the path, rest is optional metadata
            let Some(file_path) = trimmed.split_whitespace().next() else {
                continue;
            };
            let full = root.join(file_path);
            if full.exists() {
                files.push(full);
            } else {
                missing_count += 1;
                if missing_examples.len() < MAX_MISSING_PATH_EXAMPLES {
                    missing_examples.push(full);
                }
            }
        }
        if missing_count > 0 {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "list_file {list_path} is incomplete: {}/{} benchmarks are missing: {}",
                    missing_count,
                    total,
                    summarize_missing_paths(&missing_examples, missing_count)
                ),
            });
        }
        files.sort();
        ensure_unique_benchmark_paths(&files, "list_file")?;
        return Ok(Some(files));
    }

    if let Some(ref set_name) = inputs.set_file {
        let set_path = benchmarks_dir.join(set_name);
        let text = crate::resource::read_bounded_text(
            &set_path,
            crate::resource::MAX_METADATA_BYTES,
            "benchmark set file",
        )?;
        let mut files = Vec::new();
        let mut total = 0usize;
        let mut missing_count = 0usize;
        let mut missing_examples = Vec::new();
        for line in text.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            total = total
                .checked_add(1)
                .ok_or_else(|| BenchError::InvalidArgs {
                    reason: format!("set_file {set_name} contains too many entries"),
                })?;
            if total > MAX_MANIFEST_BENCHMARKS {
                return Err(BenchError::InvalidArgs {
                    reason: format!(
                        "set_file {set_name} exceeds the {MAX_MANIFEST_BENCHMARKS} benchmark limit"
                    ),
                });
            }
            // CHC-COMP set files list .yml paths; convert to .smt2
            let smt2_name = if let Some(stem) = trimmed.strip_suffix(".yml") {
                format!("{stem}.smt2")
            } else {
                trimmed.to_string()
            };
            let full = benchmarks_dir.join(&smt2_name);
            if full.exists() {
                files.push(full);
            } else {
                missing_count += 1;
                if missing_examples.len() < MAX_MISSING_PATH_EXAMPLES {
                    missing_examples.push(full);
                }
            }
        }
        if missing_count > 0 {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "set_file {set_name} is incomplete: {}/{} benchmarks are missing: {}",
                    missing_count,
                    total,
                    summarize_missing_paths(&missing_examples, missing_count)
                ),
            });
        }
        files.sort();
        ensure_unique_benchmark_paths(&files, "set_file")?;
        return Ok(Some(files));
    }

    Ok(None)
}

fn summarize_missing_paths(paths: &[PathBuf], total_missing: usize) -> String {
    let examples = paths
        .iter()
        .take(MAX_MISSING_PATH_EXAMPLES)
        .map(|path| path.display().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    if total_missing > paths.len() {
        format!("{examples}, ... ({} more)", total_missing - paths.len())
    } else {
        examples
    }
}

/// Build file list from suite_dirs — discover benchmarks from listed subdirectories only.
fn build_suite_dirs_list(
    spec: &EvalSpec,
    benchmarks_dir: &Path,
    domain: &str,
) -> Result<Option<Vec<PathBuf>>> {
    let Some(dirs) = spec
        .inputs
        .as_ref()
        .and_then(|inputs| inputs.suite_dirs.as_ref())
    else {
        return Ok(None);
    };
    if dirs.is_empty() {
        return Err(BenchError::InvalidArgs {
            reason: "suite_dirs is present but empty".to_string(),
        });
    }
    let mut files = Vec::new();
    for subdir in dirs {
        let path = benchmarks_dir.join(subdir);
        if !path.is_dir() {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "suite_dirs entry is missing or not a directory: {}",
                    path.display()
                ),
            });
        }
        files.extend(crate::native::discover_benchmarks(&path, domain)?);
    }
    files.sort();
    ensure_unique_benchmark_paths(&files, "suite_dirs")?;
    Ok(Some(files))
}

fn ensure_unique_benchmark_paths(files: &[PathBuf], source: &str) -> Result<()> {
    let mut seen = std::collections::BTreeMap::new();
    for file in files {
        let canonical = std::fs::canonicalize(file)
            .with_bench_context(|| format!("canonicalizing {source} entry {}", file.display()))?;
        if let Some(previous) = seen.insert(canonical.clone(), file.clone()) {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "{source} contains duplicate benchmark paths {} and {} (both resolve to {})",
                    previous.display(),
                    file.display(),
                    canonical.display()
                ),
            });
        }
    }
    Ok(())
}

/// Expand `~` prefix to the user's home directory. If the path does not start
/// with `~`, treat it as relative to `root`.
fn expand_tilde(path: &str, root: &Path) -> PathBuf {
    if let Some(rest) = path.strip_prefix("~/") {
        if let Some(home) = std::env::var_os("HOME") {
            PathBuf::from(home).join(rest)
        } else {
            root.join(path)
        }
    } else {
        root.join(path)
    }
}

/// Return a YAML scalar with an inline comment removed, preserving its quoting.
fn yaml_value_without_comment(raw: &str) -> &str {
    let trimmed = raw.trim();
    // Strip an inline comment marker only outside quoted scalars. A path or ID
    // such as `"case #1"` must not be silently truncated into a different
    // registry value.
    let bytes = trimmed.as_bytes();
    let mut quote = None;
    let mut index = 0usize;
    let mut comment_at = None;
    while index < bytes.len() {
        let byte = bytes[index];
        match quote {
            Some(b'"') if byte == b'\\' => {
                index = index.saturating_add(2);
                continue;
            }
            Some(b'\'') if byte == b'\'' && bytes.get(index + 1) == Some(&b'\'') => {
                index += 2;
                continue;
            }
            Some(active) if byte == active => quote = None,
            Some(_) => {}
            None if matches!(byte, b'"' | b'\'') => quote = Some(byte),
            None if byte == b'#' && (index == 0 || bytes[index - 1].is_ascii_whitespace()) => {
                comment_at = Some(index);
                break;
            }
            None => {}
        }
        index += 1;
    }
    comment_at
        .map(|offset| &trimmed[..offset])
        .unwrap_or(trimmed)
        .trim()
}

/// Strip simple YAML quoting and inline comments from a value string.
///
/// Production string fields use [`parse_eval_string_scalar`] so malformed or
/// escaped quoting cannot be misinterpreted. This helper remains useful for
/// focused lexical tests and deliberately supports only unescaped outer quotes.
#[cfg(test)]
fn strip_yaml_value(raw: &str) -> String {
    let no_comment = yaml_value_without_comment(raw);
    // Strip surrounding quotes
    if no_comment.len() >= 2
        && ((no_comment.starts_with('"') && no_comment.ends_with('"'))
            || (no_comment.starts_with('\'') && no_comment.ends_with('\'')))
    {
        no_comment[1..no_comment.len() - 1].to_string()
    } else {
        no_comment.to_string()
    }
}

// ===================================================================
// Tests
// ===================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn test_run_args() -> RunArgs {
        RunArgs {
            eval_ids: Vec::new(),
            all: false,
            domain: None,
            competition: false,
            ay: PathBuf::from("target/debug/ay"),
            timeout: None,
            output: None,
            runs: None,
            shard_index: None,
            shard_size: None,
            reference_solvers: Vec::new(),
            run_class: None,
            quiet: true,
            with_features: false,
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
        }
    }

    #[test]
    fn test_resolve_results_root_defaults_under_repo() {
        let repo = Path::new("/tmp/ay-repo");

        assert_eq!(
            resolve_results_root(repo, None),
            PathBuf::from("/tmp/ay-repo/evals/results")
        );
        assert_eq!(
            resolve_results_root(repo, Some(PathBuf::new())),
            PathBuf::from("/tmp/ay-repo/evals/results")
        );
    }

    #[test]
    fn test_resolve_results_root_honors_relative_and_absolute_override() {
        let repo = Path::new("/tmp/ay-repo");

        assert_eq!(
            resolve_results_root(repo, Some(PathBuf::from("bench-results"))),
            PathBuf::from("/tmp/ay-repo/bench-results")
        );
        assert_eq!(
            resolve_results_root(repo, Some(PathBuf::from("/tmp/ay-bench-results"))),
            PathBuf::from("/tmp/ay-bench-results")
        );
    }

    #[test]
    fn missing_path_diagnostics_are_bounded() {
        let paths = (0..100)
            .map(|index| PathBuf::from(format!("missing-{index}.smt2")))
            .collect::<Vec<_>>();
        let summary = summarize_missing_paths(&paths[..MAX_MISSING_PATH_EXAMPLES], paths.len());
        assert!(summary.contains("missing-0.smt2"));
        assert!(summary.contains("92 more"));
        assert!(!summary.contains("missing-99.smt2"));
    }

    #[test]
    fn solver_args_leave_planned_memory_to_native_execution() {
        let args = test_run_args();
        let solver_args = solver_args_for_eval("smt", &args);
        assert!(!solver_args.iter().any(|arg| arg.starts_with("--memory")));
    }

    #[test]
    fn test_infer_domain() {
        assert_eq!(infer_domain("sat-par2-dev"), "sat");
        assert_eq!(infer_domain("smt-smtcomp-qf-lia"), "smt");
        assert_eq!(infer_domain("smt-local-suite"), "smt");
        assert_eq!(infer_domain("chccomp-2025-lia"), "chc");
        assert_eq!(infer_domain("chc-something"), "chc");
        assert_eq!(infer_domain("hwmcc-wordlevel-bv-2025"), "hwmcc");
        assert_eq!(infer_domain("other"), "unknown");
        // Security benchmark domains
        assert_eq!(infer_domain("sygus-security-inv"), "sygus");
        assert_eq!(infer_domain("maxsat-eval-2023"), "maxsat");
        assert_eq!(infer_domain("qbf-qbflib"), "qbf");
        assert_eq!(infer_domain("allsat-security-cnf"), "allsat");
        assert_eq!(infer_domain("counting-security-qif"), "counting");
        assert_eq!(infer_domain("omt-security-lra"), "omt");
        assert_eq!(infer_domain("security-sygus-inv"), "sygus");
        assert_eq!(infer_domain("security-omt-lra"), "omt");
        assert_eq!(infer_domain("security-svcomp-bv"), "smt");
    }

    #[test]
    fn test_infer_competition() {
        assert_eq!(infer_competition("sat-par2-dev"), Competition::SatComp);
        assert_eq!(infer_competition("smt-local-suite"), Competition::SmtComp);
        assert_eq!(infer_competition("chccomp-2025-lia"), Competition::ChcComp);
        assert_eq!(
            infer_competition("hwmcc-wordlevel-bv-2025"),
            Competition::HwmccComp,
        );
        assert_eq!(infer_competition("unknown-eval"), Competition::SmtComp);
    }

    #[test]
    fn test_infer_hwmcc_track() {
        assert_eq!(infer_hwmcc_track("hwmcc-wordlevel-bv-2025"), "wordlevel-bv");
        assert_eq!(
            infer_hwmcc_track("hwmcc-wordlevel-array-2025"),
            "wordlevel-array"
        );
        assert_eq!(infer_hwmcc_track("hwmcc-bitlevel-2024"), "bitlevel");
        assert_eq!(infer_hwmcc_track("hwmcc-other"), "unknown");
    }

    #[test]
    fn test_infer_division() {
        assert_eq!(infer_division("smt-smtcomp-qf-lia"), "QF_LIA");
        assert_eq!(infer_division("smt-smtcomp-qf-bv"), "QF_BV");
        assert_eq!(infer_division("smt-local-suite"), "mixed");
        assert_eq!(infer_division("smt-local-qf-lia"), "QF_LIA");
        assert_eq!(infer_division("chccomp-2025-lia"), "unknown");
    }

    #[test]
    fn test_infer_track() {
        assert_eq!(
            infer_track("chccomp-2025-extra-small-lia"),
            "LIA-extra-small"
        );
        assert_eq!(infer_track("chccomp-2025-lia-lin"), "LIA-Lin");
        assert_eq!(infer_track("chccomp-2025-lia"), "LIA");
        assert_eq!(infer_track("sat-par2-dev"), "unknown");
    }

    #[test]
    fn test_strip_yaml_value() {
        assert_eq!(strip_yaml_value(" hello "), "hello");
        assert_eq!(strip_yaml_value(" \"quoted\" "), "quoted");
        assert_eq!(strip_yaml_value(" 'single' "), "single");
        assert_eq!(strip_yaml_value(" 60 # seconds "), "60");
        assert_eq!(strip_yaml_value(" value#nospace "), "value#nospace");
        assert_eq!(strip_yaml_value(" \"case #1\" # note "), "case #1");
        assert_eq!(strip_yaml_value("'case #2' # note"), "case #2");
    }

    #[test]
    fn eval_string_scalars_are_semantic_or_rejected() {
        let path = Path::new("eval.yaml");
        assert_eq!(
            eval_string_value(" 'it''s-safe' # note", "id", path, 1).unwrap(),
            "it's-safe"
        );
        assert_eq!(
            eval_string_value(" \"case #1\" # note", "id", path, 1).unwrap(),
            "case #1"
        );
        for raw in [
            "\"a\\nb\"",
            "\"a\" trailing",
            "'unterminated",
            "\"unterminated",
        ] {
            assert!(
                eval_string_value(raw, "id", path, 1).is_err(),
                "accepted malformed/unsupported scalar {raw:?}"
            );
        }
    }

    #[test]
    fn test_parse_eval_spec_rejects_wrong_scope_duplicates_and_bad_numbers() {
        for yaml in [
            "id: test\ntimeout_sec: 1\ninputs:\n",
            "id: first\nid: second\ninputs:\n",
            "id: test\ninputs:\n  timeout_sec: nope\n",
            "id: test\ninputs:\n  timeout_sec: NaN\n",
            "id: test\ninputs:\n  timeout_sec: \"5\"\n",
            "id: test\ninputs:\n  runs: 0\n",
            "id: test\ninputs:\n  runs: '1'\n",
            "id: test\ninputs:\n  runs: 1\n  runs: 2\n",
            "id: test\ninputs:\n  timeout_secs: 5\n",
            "id: test\ninputs:\n  benchmarks_dir: >\n    benchmarks/sat\n",
            "id: test\ninputs:\n  benchmarks_dir: null\n",
            "id: test\ninputs:\n  timeout_sec: 5\n    ignored: true\n",
            "id: test\ninputs:\n  suite_dirs: []\n    - silently-ignored\n",
            "id: test\ninputs:\n  suite_dirs: \"[]\"\n",
            "id: test\ninputs:\n  list_file: cases.txt\n  set_file: cases.set\n",
            "id: test\ninputs:\n  list_file: cases.txt\n  suite_dirs:\n    - cases\n",
            "id: ../escape\ninputs:\n",
            "id: test\n",
        ] {
            assert!(
                parse_eval_spec_minimal(yaml, Path::new("bad.yaml")).is_err(),
                "registry parser accepted {yaml:?}"
            );
        }
    }

    #[test]
    fn test_parse_eval_spec_does_not_adopt_other_section_fields() {
        let yaml = "\
id: test
inputs:
  timeout_sec: 5
outputs:
  metadata:
    timeout_sec: 777
";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.inputs.unwrap().timeout_sec, Some(5.0));
    }

    #[test]
    fn test_validate_eval_id_accepts_only_path_safe_ascii() {
        for valid in ["sat-main", "SMT_2026.1", "a"] {
            validate_eval_id(valid, Path::new("eval.yaml")).unwrap();
        }
        for invalid in ["", ".", "..", "../x", "a/b", "a b", "café"] {
            assert!(validate_eval_id(invalid, Path::new("eval.yaml")).is_err());
        }
    }

    #[cfg(unix)]
    #[test]
    fn explicit_solver_paths_must_be_executable_regular_files() {
        use std::os::unix::fs::PermissionsExt as _;

        let directory = tempfile::tempdir().unwrap();
        let solver = directory.path().join("solver");
        std::fs::write(&solver, b"#!/bin/sh\nexit 0\n").unwrap();
        let mut permissions = std::fs::metadata(&solver).unwrap().permissions();
        permissions.set_mode(0o600);
        std::fs::set_permissions(&solver, permissions.clone()).unwrap();
        assert!(find_solver(solver.to_str().unwrap()).is_none());

        permissions.set_mode(0o700);
        std::fs::set_permissions(&solver, permissions).unwrap();
        assert_eq!(find_solver(solver.to_str().unwrap()), Some(solver));
        assert!(!is_executable_file(directory.path()));
    }

    #[test]
    fn explicitly_configured_missing_reference_solver_fails_closed() {
        let error = resolve_configured_reference_solver(
            "definitely-missing-ay-bench-reference-solver-4f97e98a",
        )
        .expect_err("configured reference must resolve");
        assert!(error.to_string().contains("definitely-missing"));
    }

    #[test]
    fn duplicate_eval_ids_are_rejected_with_both_sources() {
        let mut seen = BTreeMap::new();
        register_eval_id(&mut seen, "same", Path::new("first.yaml")).unwrap();
        let error = register_eval_id(&mut seen, "same", Path::new("second.yaml"))
            .expect_err("duplicate ID must fail")
            .to_string();
        assert!(error.contains("first.yaml"), "got: {error}");
        assert!(error.contains("second.yaml"), "got: {error}");
    }

    #[test]
    fn eval_registry_directory_scan_is_sorted_and_bounded() {
        let directory = tempfile::tempdir().unwrap();
        std::fs::write(directory.path().join("b.yaml"), b"inputs:\n").unwrap();
        std::fs::write(directory.path().join("a.yaml"), b"inputs:\n").unwrap();

        let paths = bounded_sorted_registry_paths_with_limit(directory.path(), 2).unwrap();
        assert_eq!(paths[0].file_name().unwrap(), "a.yaml");
        assert_eq!(paths[1].file_name().unwrap(), "b.yaml");

        std::fs::write(directory.path().join("c.yaml"), b"inputs:\n").unwrap();
        assert!(bounded_sorted_registry_paths_with_limit(directory.path(), 2).is_err());
    }

    #[test]
    fn test_parse_eval_spec_minimal() {
        let yaml = "\
id: sat-par2-dev
version: 1
inputs:
  timeout_sec: 20
  benchmarks_dir: benchmarks/sat/sample
";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.id.as_deref(), Some("sat-par2-dev"));
        let inputs = spec.inputs.unwrap();
        assert_eq!(inputs.timeout_sec, Some(20.0));
        assert_eq!(
            inputs.benchmarks_dir.as_deref(),
            Some("benchmarks/sat/sample")
        );
    }

    #[test]
    fn test_parse_eval_spec_sat_comp_metadata() {
        let yaml = "\
id: sat-par2-dev
competition: sat-comp
scoring: sat-comp
inputs:
  timeout_sec: 20
  standard_timeout_sec: 5000
  benchmarks_dir: benchmarks/sat/sample
";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.competition.as_deref(), Some("sat-comp"));
        assert_eq!(spec.scoring.as_deref(), Some("sat-comp"));
        let inputs = spec.inputs.as_ref().unwrap();
        assert_eq!(inputs.timeout_sec, Some(20.0));
        assert_eq!(inputs.standard_timeout_sec, Some(5000.0));
        assert_eq!(scoring_label("sat-par2-dev", &spec), "sat-comp");
        assert_eq!(standard_timeout_sec("sat-par2-dev", &spec), 5000.0);
    }

    #[test]
    fn test_parse_eval_spec_quoted_id() {
        let yaml = "id: \"my-eval\"\ninputs:\n  timeout_sec: 30\n";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.id.as_deref(), Some("my-eval"));
    }

    #[test]
    fn test_parse_eval_spec_inline_comment() {
        let yaml = "id: eval1\ninputs:\n  timeout_sec: 60 # seconds\n";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.inputs.unwrap().timeout_sec, Some(60.0));
    }

    #[test]
    fn test_parse_eval_spec_fallback_id() {
        let yaml = "inputs:\n  timeout_sec: 10\n";
        let spec =
            parse_eval_spec_minimal(yaml, Path::new("/evals/registry/my-eval.yaml")).unwrap();
        assert_eq!(spec.id.as_deref(), Some("my-eval"));
    }

    #[test]
    fn test_parse_eval_spec_runs() {
        let yaml = "id: test\ninputs:\n  runs: 3\n  timeout_sec: 20\n";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.inputs.unwrap().runs, Some(3));
    }

    #[test]
    fn test_effective_runs_uses_yaml_when_cli_omitted() {
        let yaml = "id: test\ninputs:\n  runs: 3\n  timeout_sec: 20\n";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        let args = RunArgs {
            runs: None,
            ..test_run_args()
        };

        assert_eq!(effective_runs(&args, spec.inputs.as_ref()).unwrap(), 3);
    }

    #[test]
    fn test_effective_runs_respects_explicit_single_run_override() {
        let yaml = "id: test\ninputs:\n  runs: 3\n  timeout_sec: 20\n  reference_solver: z3\n";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        let args = RunArgs {
            runs: Some(1),
            reference_solvers: vec![("z3".to_string(), PathBuf::from("z3"))],
            ..test_run_args()
        };

        assert_eq!(effective_runs(&args, spec.inputs.as_ref()).unwrap(), 1);
    }

    #[test]
    fn test_effective_runs_rejects_programmatic_zero_override() {
        let args = RunArgs {
            runs: Some(0),
            ..test_run_args()
        };
        assert!(effective_runs(&args, None).is_err());
    }

    #[test]
    fn test_parse_eval_spec_suite_dirs() {
        let yaml = "\
id: smt-local-suite
inputs:
  benchmarks_dir: benchmarks/smt/
  suite_dirs:
    - QF_BV
    - QF_LIA
    - QF_LRA
  timeout_sec: 30
";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        let inputs = spec.inputs.unwrap();
        let dirs = inputs.suite_dirs.unwrap();
        assert_eq!(dirs, vec!["QF_BV", "QF_LIA", "QF_LRA"]);
    }

    #[test]
    fn test_parse_eval_spec_reference_solver() {
        let yaml = "id: sat-par2-dev\ninputs:\n  reference_solver: z3\n  timeout_sec: 20\n";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(spec.inputs.unwrap().reference_solver.as_deref(), Some("z3"));
    }

    #[test]
    fn test_parse_eval_spec_consensus_csv() {
        let yaml = "\
id: hwmcc-wordlevel-bv-2025
inputs:
  consensus_csv: ~/labels/hwmcc25-wordlevel-bv.csv
  timeout_sec: 30
";
        let spec = parse_eval_spec_minimal(yaml, Path::new("test.yaml")).unwrap();
        assert_eq!(
            spec.inputs.unwrap().consensus_csv.as_deref(),
            Some("~/labels/hwmcc25-wordlevel-bv.csv")
        );
    }

    #[test]
    fn test_eval_list_row_uses_sat_comp_registry_metadata() {
        let yaml = "\
id: sat-par2-dev
competition: sat-comp
scoring: sat-comp
inputs:
  timeout_sec: 20
  standard_timeout_sec: 5000
";
        let spec = parse_eval_spec_minimal(yaml, Path::new("sat-par2-dev.yaml")).unwrap();
        let rows = eval_list_rows(&[("sat-par2-dev".to_string(), spec)]);

        assert_eq!(
            rows,
            vec![EvalListRow {
                eval_id: "sat-par2-dev".to_string(),
                domain: "sat".to_string(),
                scoring: "sat-comp".to_string(),
                dev_timeout: "20s".to_string(),
                standard_timeout: "5000s".to_string(),
            }]
        );
    }

    #[test]
    fn test_discover_sat_par2_registry_specs() {
        let evals = discover_evals().unwrap();
        let dev = evals
            .iter()
            .find(|(id, _)| id == "sat-par2-dev")
            .expect("sat-par2-dev registry spec should exist");
        let heldout = evals
            .iter()
            .find(|(id, _)| id == "sat-par2-heldout")
            .expect("sat-par2-heldout registry spec should exist");

        for (eval_id, spec) in [dev, heldout] {
            assert_eq!(infer_domain(eval_id), "sat");
            assert_eq!(infer_competition(eval_id), Competition::SatComp);
            assert_eq!(scoring_label(eval_id, spec), "sat-comp");
            assert_eq!(standard_timeout_sec(eval_id, spec), 5000.0);
        }
    }

    #[test]
    fn test_select_sat_domain_evals_for_run() {
        let evals = discover_evals().unwrap();
        let args = RunArgs {
            eval_ids: Vec::new(),
            all: false,
            domain: Some("sat".to_string()),
            competition: false,
            ay: PathBuf::from("target/debug/ay"),
            timeout: None,
            output: None,
            runs: None,
            shard_index: None,
            shard_size: None,
            reference_solvers: Vec::new(),
            run_class: None,
            quiet: true,
            with_features: false,
            sat_track: None,
            sat_ai_class: None,
            sat_variant: None,
        };

        let selected = select_evals_for_run(evals, &args).unwrap();
        let ids: Vec<_> = selected.iter().map(|(id, _)| id.as_str()).collect();
        assert!(ids.contains(&"sat-par2-dev"));
        assert!(ids.contains(&"sat-par2-heldout"));
        assert!(selected
            .iter()
            .all(|(eval_id, _)| infer_domain(eval_id) == "sat"));
    }

    #[test]
    fn test_validate_run_class_rejects_unrecognized_library_value() {
        assert!(validate_run_class(None).is_ok());
        assert!(validate_run_class(Some("replay")).is_ok());
        assert!(validate_run_class(Some("laptop")).is_ok());
        let error = validate_run_class(Some("desktop")).expect_err("invalid class");
        assert!(error.to_string().contains("desktop"));
    }

    #[test]
    fn shard_selection_requires_a_complete_bounded_pair() {
        let none = test_run_args();
        assert_eq!(shard_selection(&none).unwrap(), None);

        let missing_size = RunArgs {
            shard_index: Some(0),
            ..test_run_args()
        };
        assert!(shard_selection(&missing_size).is_err());

        let missing_index = RunArgs {
            shard_size: Some(64),
            ..test_run_args()
        };
        assert!(shard_selection(&missing_index).is_err());

        let zero = RunArgs {
            shard_index: Some(0),
            shard_size: Some(0),
            ..test_run_args()
        };
        assert!(shard_selection(&zero).is_err());

        let selected = RunArgs {
            shard_index: Some(7),
            shard_size: Some(64),
            ..test_run_args()
        };
        assert_eq!(
            shard_selection(&selected).unwrap(),
            Some(crate::native::NativeShardSelection { index: 7, size: 64 })
        );
    }

    #[test]
    fn test_later_reference_disagreement_overrides_first_agreement() {
        let mut item = crate::native::NativeResultItem {
            file: "case.smt2".to_string(),
            benchmark_path: "case.smt2".to_string(),
            benchmark_content_hash: None,
            solver_input_hash: None,
            solver_input_path: None,
            expected: None,
            expected_source: "unknown".to_string(),
            result: "sat".to_string(),
            harness_error: None,
            time_sec: 0.1,
            cpu_time_sec: 0.1,
            cpu_time_source: "test".to_string(),
            exit_code: Some(0),
            solver_argv: Vec::new(),
            solver_env: Default::default(),
            artifacts: None,
            sat_run: None,
            extracted_features: None,
        };
        let comparisons = BTreeMap::from([("case.smt2", vec!["agree", "disagree"])]);
        assert_eq!(classify_verifier(&item, &comparisons), 0);

        item.expected = Some("sat".to_string());
        assert_eq!(classify_verifier(&item, &BTreeMap::new()), -1);
        item.expected_source = "header".to_string();
        assert_eq!(classify_verifier(&item, &BTreeMap::new()), 1);
    }

    #[test]
    fn test_expand_tilde() {
        let root = Path::new("/repo");
        // Non-tilde path joins with root
        assert_eq!(
            expand_tilde("benchmarks/sat", root),
            root.join("benchmarks/sat")
        );
        // Tilde path expands home
        let home = std::env::var_os("HOME").unwrap();
        let expected = PathBuf::from(&home).join("hwmcc/benchmarks");
        assert_eq!(expand_tilde("~/hwmcc/benchmarks", root), expected);
    }

    #[test]
    fn test_build_rows_persists_sat_artifact_metadata() {
        let artifact_output_dir = "/tmp/ay-bench/artifacts".to_string();
        let proof_hash = "fh128:0123456789abcdef0123456789abcdef".to_string();
        let item = crate::native::NativeResultItem {
            file: "proof.cnf".to_string(),
            benchmark_path: "proof.cnf".to_string(),
            benchmark_content_hash: Some("fh128:proof".to_string()),
            solver_input_hash: None,
            solver_input_path: None,
            expected: Some("unsat".to_string()),
            expected_source: "path".to_string(),
            result: "unsat".to_string(),
            harness_error: None,
            time_sec: 0.25,
            cpu_time_sec: 0.25,
            cpu_time_source: "test".to_string(),
            exit_code: Some(20),
            solver_argv: Vec::new(),
            solver_env: Default::default(),
            artifacts: Some(crate::native::SolverArtifactMetadata {
                output_dir: artifact_output_dir.clone(),
                proof_path: Some("/tmp/ay-bench/artifacts/proof.lrat".to_string()),
                proof_format: Some("lrat".to_string()),
                proof_exists: Some(true),
                proof_bytes: Some(128),
                proof_hash: Some(proof_hash.clone()),
                proof_validation: "unchecked".to_string(),
            }),
            sat_run: None,
            extracted_features: None,
        };
        let missing_proof_item = crate::native::NativeResultItem {
            file: "missing.cnf".to_string(),
            benchmark_path: "missing.cnf".to_string(),
            benchmark_content_hash: Some("fh128:missing".to_string()),
            solver_input_hash: None,
            solver_input_path: None,
            expected: Some("unsat".to_string()),
            expected_source: "path".to_string(),
            result: "unsat".to_string(),
            harness_error: None,
            time_sec: 0.5,
            cpu_time_sec: 0.5,
            cpu_time_source: "test".to_string(),
            exit_code: Some(20),
            solver_argv: Vec::new(),
            solver_env: Default::default(),
            artifacts: Some(crate::native::SolverArtifactMetadata {
                output_dir: artifact_output_dir.clone(),
                proof_path: Some("/tmp/ay-bench/artifacts/missing.lrat".to_string()),
                proof_format: Some("lrat".to_string()),
                proof_exists: Some(false),
                proof_bytes: None,
                proof_hash: None,
                proof_validation: "not-emitted".to_string(),
            }),
            sat_run: None,
            extracted_features: None,
        };
        let results = crate::native::NativeResults {
            environment: crate::environment::Environment {
                timestamp: "2026-04-25T00:00:00Z".to_string(),
                git_commit: "commit".to_string(),
                git_dirty: Some(false),
                comparable_git_state: false,
                ay_path: "ay".to_string(),
                ay_sha256:
                    "sha256:0000000000000000000000000000000000000000000000000000000000000000"
                        .to_string(),
                ay_size_bytes: 1,
                ay_version: "ay test".to_string(),
                ay_build_version: "test".to_string(),
                ay_build_commit: "commit".to_string(),
                ay_build_datetime_utc: "2026-04-25T00:00:00Z".to_string(),
                ay_build_stamp: "test".to_string(),
                hostname: "host".to_string(),
                os: "test",
                arch: "test",
                cpu_model: "cpu".to_string(),
                cpu_count: 1,
                memory_bytes: 1,
                load_avg: [0.0, 0.0, 0.0],
            },
            items: vec![item, missing_proof_item],
            preprocessing: Vec::new(),
            settings: crate::native::NativeSettings {
                benchmarks_dir: ".".to_string(),
                timeout_sec: 1.0,
                domain: "sat".to_string(),
                benchmark_count: 2,
                runs: 1,
                solver_args: Vec::new(),
                solver_env: Default::default(),
                artifact_output_dir: Some(artifact_output_dir.clone()),
                artifact_max_bytes: Some(8 * 1024 * 1024 * 1024),
                artifact_size_enforcement: Some("test".to_string()),
                sat_track: Some("main".to_string()),
                sat_ai_class: Some("regular".to_string()),
                sat_variant: Some("default".to_string()),
                sat_competition_profile: None,
                resource_plan: Some(crate::resource::ResourcePlan {
                    requested_jobs: 1,
                    jobs: 1,
                    memlimit_mb_per_child: 1024,
                    nbcore_per_child: 1,
                    headroom_mb: 256,
                    planner: "test".to_string(),
                }),
                resource_enforcement: Some(crate::resource::ENFORCEMENT_AY_MEMORY_V1.to_string()),
                shard: None,
            },
            comparison: None,
            comparisons: None,
            reference_comparisons: None,
            run_class: None,
            run_class_verified: None,
            host_fingerprint: None,
            references: None,
        };

        let feature_error = build_rows("commit", "sat-main", &results, true)
            .expect_err("requested missing features must fail closed");
        assert!(feature_error
            .to_string()
            .contains("feature evidence is missing"));

        let rows = build_rows("commit", "sat-main", &results, false).expect("build rows");

        assert_eq!(rows.len(), 2);
        assert_eq!(
            rows[0].artifact_output_dir.as_deref(),
            Some(artifact_output_dir.as_str())
        );
        assert_eq!(
            rows[0].proof_path.as_deref(),
            Some("/tmp/ay-bench/artifacts/proof.lrat")
        );
        assert_eq!(rows[0].proof_format.as_deref(), Some("lrat"));
        assert_eq!(rows[0].proof_exists, Some(true));
        assert_eq!(rows[0].proof_bytes, Some(128));
        assert_eq!(rows[0].proof_hash.as_deref(), Some(proof_hash.as_str()));
        assert_eq!(rows[0].proof_validation.as_deref(), Some("unchecked"));
        assert_eq!(
            rows[1].artifact_output_dir.as_deref(),
            Some(artifact_output_dir.as_str())
        );
        assert_eq!(
            rows[1].proof_path.as_deref(),
            Some("/tmp/ay-bench/artifacts/missing.lrat")
        );
        assert_eq!(rows[1].proof_format.as_deref(), Some("lrat"));
        assert_eq!(rows[1].proof_exists, Some(false));
        assert_eq!(rows[1].proof_bytes, None);
        assert_eq!(rows[1].proof_hash, None);
        assert_eq!(rows[1].proof_validation.as_deref(), Some("not-emitted"));
    }

    #[test]
    fn test_select_representative_single() {
        let item = crate::native::NativeResultItem {
            file: "test.cnf".to_string(),
            benchmark_path: "test.cnf".to_string(),
            benchmark_content_hash: Some("fh128:test".to_string()),
            solver_input_hash: None,
            solver_input_path: None,
            expected: None,
            expected_source: "unknown".to_string(),
            result: "sat".to_string(),
            harness_error: None,
            time_sec: 1.5,
            cpu_time_sec: 1.5,
            cpu_time_source: "test".to_string(),
            exit_code: Some(10),
            solver_argv: Vec::new(),
            solver_env: Default::default(),
            artifacts: None,
            sat_run: None,
            extracted_features: None,
        };
        let rep = crate::native::select_representative(vec![item]).expect("representative");
        assert_eq!(rep.time_sec, 1.5);
    }

    #[test]
    fn test_select_representative_median() {
        let make = |t: f64| crate::native::NativeResultItem {
            file: "test.cnf".to_string(),
            benchmark_path: "test.cnf".to_string(),
            benchmark_content_hash: Some("fh128:test".to_string()),
            solver_input_hash: None,
            solver_input_path: None,
            expected: None,
            expected_source: "unknown".to_string(),
            result: "sat".to_string(),
            harness_error: None,
            time_sec: t,
            cpu_time_sec: t,
            cpu_time_source: "test".to_string(),
            exit_code: Some(10),
            solver_argv: Vec::new(),
            solver_env: Default::default(),
            artifacts: None,
            sat_run: None,
            extracted_features: None,
        };
        // 3 runs: 1.0, 3.0, 2.0 — median is 2.0
        let rep = crate::native::select_representative(vec![make(1.0), make(3.0), make(2.0)])
            .expect("representative");
        assert_eq!(rep.time_sec, 2.0);
    }

    #[test]
    fn test_select_representative_rejects_mixed_classifications() {
        let make = |result: &str, time_sec: f64| crate::native::NativeResultItem {
            file: "test.cnf".to_string(),
            benchmark_path: "test.cnf".to_string(),
            benchmark_content_hash: Some("sha256:test".to_string()),
            solver_input_hash: None,
            solver_input_path: None,
            expected: None,
            expected_source: "unknown".to_string(),
            result: result.to_string(),
            harness_error: None,
            time_sec,
            cpu_time_sec: time_sec,
            cpu_time_source: "test".to_string(),
            exit_code: Some(0),
            solver_argv: Vec::new(),
            solver_env: Default::default(),
            artifacts: None,
            sat_run: None,
            extracted_features: None,
        };
        let error = crate::native::select_representative(vec![
            make("sat", 1.0),
            make("unsat", 2.0),
            make("sat", 3.0),
        ])
        .expect_err("mixed verdicts must fail closed");
        assert!(error.to_string().contains("mixed classifications"));
    }
}
