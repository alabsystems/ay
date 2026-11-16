// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Current-release semantic consumers, distinct from the historical census.
//!
//! These fixed paired witnesses exercise real transformations, probe branches,
//! printer parameter effects and attached-simplifier consumers. The complete
//! authenticated catalogs remain the denominator: untested entries, additional
//! argument shapes and model-converter behavior remain explicit gaps.

use super::*;

const SCHEMA: &str = "ay-current-z3-behavior/v1";
const MAX_REPORT_BYTES: u64 = 32 * 1024 * 1024;

enum Provider {
    Ay,
    Z3,
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(rename_all = "kebab-case")]
enum Expectation {
    Goals,
    TacticFailure,
    Sat,
    Unsat,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
struct Case {
    id: String,
    category: String,
    name: String,
    scope: String,
    candidate: String,
    control: String,
    candidate_expected: Expectation,
    control_expected: Expectation,
    require_goal_change: bool,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
struct Capture {
    exit_code: Option<i32>,
    timed_out: bool,
    memout: bool,
    stdin_complete: bool,
    stdout_truncated: bool,
    stderr_truncated: bool,
    stdout_utf8: bool,
    stderr_utf8: bool,
    stdout: String,
    stderr: String,
    stdout_sha256: String,
    stderr_sha256: String,
}

impl Capture {
    fn from_output(output: GuardedTranscriptOutput) -> Self {
        Self {
            exit_code: output.status.and_then(|status| status.code()),
            timed_out: output.timed_out,
            memout: output.memout,
            stdin_complete: output.stdin_complete,
            stdout_truncated: output.stdout_truncated,
            stderr_truncated: output.stderr_truncated,
            stdout_utf8: std::str::from_utf8(&output.stdout).is_ok(),
            stderr_utf8: std::str::from_utf8(&output.stderr).is_ok(),
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
            stdout_sha256: sha256_bytes(&output.stdout),
            stderr_sha256: sha256_bytes(&output.stderr),
        }
    }

    fn clean(&self) -> bool {
        self.exit_code == Some(0)
            && !self.timed_out
            && !self.memout
            && self.stdin_complete
            && !self.stdout_truncated
            && !self.stderr_truncated
            && self.stdout_utf8
            && self.stderr_utf8
            && self.stderr.is_empty()
    }
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
struct CaseResult {
    case: Case,
    reference_candidate: Capture,
    reference_control: Capture,
    ay_candidate: Capture,
    ay_control: Capture,
    reference_discriminates: bool,
    passed: bool,
    failure: Option<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
struct Coverage {
    catalog_entries: usize,
    selected_names: Vec<String>,
    untested_names: Vec<String>,
    full_semantics_complete: bool,
    remaining_scope: String,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
struct Report {
    schema: String,
    profile_id: String,
    profile_sha256: String,
    inventory: Artifact,
    ay: Artifact,
    z3_sha256: String,
    timeout_seconds: u64,
    resource_envelope: String,
    cases: Vec<CaseResult>,
    coverage: BTreeMap<String, Coverage>,
    selected_checks_passed: bool,
    full_semantics_complete: bool,
}

fn pair(
    id: &str,
    category: &str,
    name: &str,
    scope: &str,
    candidate: String,
    control: String,
    candidate_expected: Expectation,
    control_expected: Expectation,
    require_goal_change: bool,
) -> Case {
    Case {
        id: id.to_string(),
        category: category.to_string(),
        name: name.to_string(),
        scope: scope.to_string(),
        candidate,
        control,
        candidate_expected,
        control_expected,
        require_goal_change,
    }
}

fn cases() -> Vec<Case> {
    let mut result = Vec::new();
    for (name, input) in [
        ("simplify", "(declare-const x Int)\n(assert (= (+ x 0) 1))\n"),
        ("solve-eqs", "(declare-const x Int)\n(declare-const y Int)\n(assert (= x 1))\n(assert (= y (+ x 2)))\n"),
        ("propagate-values", "(declare-const x Int)\n(declare-const y Int)\n(assert (= x 1))\n(assert (> y x))\n"),
        ("nnf", "(declare-const p Bool)\n(declare-const q Bool)\n(declare-const r Bool)\n(assert (not (and (or p q) r)))\n"),
        ("bit-blast", "(declare-const x (_ BitVec 3))\n(assert (= (bvadd x #b001) #b011))\n"),
    ] {
        result.push(pair(&format!("tactic.{name}"), "tactics", name,
            "one observable non-identity transformed goal; broader rewrites and model converters untested",
            format!("{input}(apply {name})\n"), format!("{input}(apply skip)\n"),
            Expectation::Goals, Expectation::Goals, true));
    }
    for (name, positive, negative) in [
        (
            "is-qfbv",
            "(declare-const x (_ BitVec 8))\n(assert (= x #x01))\n",
            "(declare-const x Int)\n(assert (> x 0))\n",
        ),
        (
            "is-qflia",
            "(declare-const x Int)\n(assert (> x 0))\n",
            "(declare-const x Real)\n(assert (> x 0.0))\n",
        ),
        (
            "is-propositional",
            "(declare-const p Bool)\n(assert p)\n",
            "(declare-const x Int)\n(assert (> x 0))\n",
        ),
    ] {
        result.push(pair(&format!("probe.{name}"), "probes", name,
            "positive and negative fail-if branches on two typed goals; additional probe domains untested",
            format!("{positive}(apply (fail-if {name}))\n"), format!("{negative}(apply (fail-if {name}))\n"),
            Expectation::TacticFailure, Expectation::Goals, false));
    }
    for name in [
        "simplify",
        "solve-eqs",
        "propagate-values",
        "elim-unconstrained",
    ] {
        result.push(pair(&format!("simplifier.{name}"), "simplifiers", name,
            "attached-simplifier SAT model value and UNSAT consumer pair only; does not establish rewrite effects or complete model conversion",
            format!("(set-simplifier {name})\n(declare-const x Int)\n(assert (= x 7))\n(check-sat)\n(get-value (x))\n"),
            format!("(set-simplifier {name})\n(declare-const x Int)\n(assert (= x 7))\n(assert (= x 8))\n(check-sat)\n"),
            Expectation::Sat, Expectation::Unsat, false));
    }
    let rational =
        "(declare-const x Real)\n(assert (= x (/ 1.0 3.0)))\n(check-sat)\n(get-value (x))\n";
    result.push(pair(
        "parameter.pp.decimal",
        "parameters",
        "pp.decimal",
        "observable exact-versus-decimal value printing; other values and defaults untested",
        format!("(set-option :pp.decimal true)\n{rational}"),
        format!("(set-option :pp.decimal false)\n{rational}"),
        Expectation::Sat,
        Expectation::Sat,
        false,
    ));
    result.push(pair(
        "parameter.pp.decimal_precision",
        "parameters",
        "pp.decimal_precision",
        "two observable decimal precision values; other values and defaults untested",
        format!("(set-option :pp.decimal true)\n(set-option :pp.decimal-precision 2)\n{rational}"),
        format!("(set-option :pp.decimal true)\n(set-option :pp.decimal-precision 8)\n{rational}"),
        Expectation::Sat,
        Expectation::Sat,
        false,
    ));
    let bv = "(declare-const x (_ BitVec 8))\n(assert (= x #x2a))\n(check-sat)\n(get-value (x))\n";
    result.push(pair("parameter.pp.bv_literals", "parameters", "pp.bv_literals", "observable hexadecimal-versus-indexed bit-vector value printing; other widths and defaults untested",
        format!("(set-option :pp.bv-literals true)\n{bv}"), format!("(set-option :pp.bv-literals false)\n{bv}"), Expectation::Sat, Expectation::Sat, false));
    result
}

/// Whitespace outside quoted tokens is insignificant; quoted payload bytes,
/// atom boundaries and parentheses remain exact (including decimal '?' text).
fn normalized(text: &str) -> Result<Vec<String>, String> {
    let bytes = text.as_bytes();
    let mut result = Vec::new();
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index].is_ascii_whitespace() {
            index += 1;
            continue;
        }
        let start = index;
        if matches!(bytes[index], b'(' | b')') {
            index += 1;
        } else if matches!(bytes[index], b'"' | b'|') {
            let delimiter = bytes[index];
            index += 1;
            loop {
                let byte = *bytes
                    .get(index)
                    .ok_or("unterminated quoted transcript token")?;
                index += 1;
                if byte == delimiter {
                    if delimiter == b'"' && bytes.get(index) == Some(&b'"') {
                        index += 1;
                    } else {
                        break;
                    }
                } else if delimiter == b'|' && byte == b'\\' {
                    index += 1;
                }
            }
        } else {
            while index < bytes.len()
                && !bytes[index].is_ascii_whitespace()
                && !matches!(bytes[index], b'(' | b')')
            {
                index += 1;
            }
        }
        result.push(
            text.get(start..index)
                .ok_or("invalid transcript UTF-8 boundary")?
                .to_string(),
        );
    }
    Ok(result)
}

fn goal_payload(text: &str) -> Result<Vec<String>, String> {
    let expression = ay_frontend::sexp::parse_sexp(text).map_err(|error| error.to_string())?;
    let roots = expression.as_list().ok_or("goals output is not a list")?;
    if !roots.first().is_some_and(|head| head.is_symbol("goals")) {
        return Err("expected goals output".to_string());
    }
    let mut payloads = Vec::new();
    for goal in &roots[1..] {
        let entries = goal.as_list().ok_or("goal is not a list")?;
        if !entries.first().is_some_and(|head| head.is_symbol("goal")) {
            return Err("expected goal entry".to_string());
        }
        let payload = entries[1..]
            .iter()
            .take_while(|entry| !matches!(entry, ay_frontend::SExpr::Keyword(_)))
            .map(ay_frontend::SExpr::to_raw_string)
            .collect::<Vec<_>>()
            .join(" ");
        payloads.push(payload);
    }
    Ok(payloads)
}

fn expectation(output: &Capture, expected: Expectation) -> bool {
    if !output.clean() {
        return false;
    }
    match expected {
        Expectation::Goals => goal_payload(&output.stdout).is_ok(),
        Expectation::TacticFailure => {
            normalized(&output.stdout).ok()
                == Some(vec![
                    "(".to_string(),
                    "error".to_string(),
                    "\"tactic failed: fail-if tactic\"".to_string(),
                    ")".to_string(),
                ])
        }
        Expectation::Sat => {
            output
                .stdout
                .lines()
                .filter(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
                .collect::<Vec<_>>()
                == ["sat"]
                && !output.stdout.contains("(error")
                && normalized(&output.stdout).is_ok_and(|tokens| {
                    tokens.get(1).is_some_and(|token| token == "(")
                        && tokens.get(2).is_some_and(|token| token == "(")
                        && tokens.get(3).is_some_and(|token| token == "x")
                })
        }
        Expectation::Unsat => output.stdout.trim() == "unsat",
    }
}

fn classify(
    case: &Case,
    reference_candidate: Capture,
    reference_control: Capture,
    ay_candidate: Capture,
    ay_control: Capture,
) -> CaseResult {
    let reference_discriminates = if case.require_goal_change {
        match (
            goal_payload(&reference_candidate.stdout),
            goal_payload(&reference_control.stdout),
        ) {
            (Ok(a), Ok(b)) => a != b,
            _ => false,
        }
    } else {
        normalized(&reference_candidate.stdout).ok() != normalized(&reference_control.stdout).ok()
    };
    let failure = if !expectation(&reference_candidate, case.candidate_expected)
        || !expectation(&reference_control, case.control_expected)
    {
        Some(
            "pinned reference did not satisfy the authored semantic witness expectations"
                .to_string(),
        )
    } else if !reference_discriminates {
        Some(
            "reference arms are not observably distinct; this is not an effect witness".to_string(),
        )
    } else if !expectation(&ay_candidate, case.candidate_expected)
        || !expectation(&ay_control, case.control_expected)
    {
        Some("AY failed a semantic witness expectation".to_string())
    } else if normalized(&reference_candidate.stdout).ok() != normalized(&ay_candidate.stdout).ok()
        || normalized(&reference_control.stdout).ok() != normalized(&ay_control.stdout).ok()
    {
        Some("AY observable results differ from pinned reference".to_string())
    } else {
        None
    };
    CaseResult {
        case: case.clone(),
        reference_candidate,
        reference_control,
        ay_candidate,
        ay_control,
        reference_discriminates,
        passed: failure.is_none(),
        failure,
    }
}

fn coverage(inventory: &Value) -> Result<BTreeMap<String, Coverage>, String> {
    let mut rows = BTreeMap::new();
    for category in ["tactics", "probes", "simplifiers", "parameters"] {
        let catalog = inventory
            .get("catalogs")
            .and_then(|value| value.get(category))
            .and_then(|value| value.get("entries"))
            .and_then(Value::as_object)
            .ok_or_else(|| format!("authenticated current inventory lacks {category}"))?;
        let names = cases()
            .iter()
            .filter(|case| case.category == category)
            .map(|case| case.name.clone())
            .collect::<BTreeSet<_>>();
        for name in &names {
            if !catalog.contains_key(name) {
                return Err(format!(
                    "selected {category} witness {name} is absent from current pinned catalog"
                ));
            }
        }
        rows.insert(category.to_string(), Coverage {
            catalog_entries: catalog.len(), selected_names: names.iter().cloned().collect(),
            untested_names: catalog.keys().filter(|name| !names.contains(*name)).cloned().collect(),
            full_semantics_complete: false,
            remaining_scope: "Unselected names and all additional argument shapes, defaults, invalid arguments, incremental effects and model-converter behavior remain unqualified. Selected simplifier witnesses establish consumer results only.".to_string(),
        });
    }
    Ok(rows)
}

fn capture(
    resources: &PlannedResources,
    program: &Path,
    input: &str,
    provider: Provider,
    timeout: Duration,
) -> Result<Capture, String> {
    let args = match provider {
        Provider::Ay => vec!["--z3-mode", "--quiet", "-in"],
        Provider::Z3 => vec!["-in"],
    };
    resources
        .run_external_transcript_scrubbed(
            program,
            args,
            input.as_bytes(),
            timeout,
            "current release paired behavioral witness",
        )
        .map(Capture::from_output)
        .map_err(|error| error.to_string())
}

fn collect(inventory_path: &Path, ay_source: &Path, timeout: u64) -> Result<Report, String> {
    let inventory_path = fs::canonicalize(inventory_path).map_err(|error| error.to_string())?;
    let bytes = read_bounded_bytes(
        &inventory_path,
        64 * 1024 * 1024,
        "current release inventory",
        true,
    )?;
    let private_inventory = tempfile::tempdir().map_err(|error| error.to_string())?;
    let private_path = private_inventory.path().join("inventory.json");
    atomic_write_new(&private_path, &bytes)?;
    current_release::check(&[private_path.to_string_lossy().into_owned()])?;
    let inventory: Value = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    let inventory_sha = sha256_bytes(&bytes);
    let profile = canonical_profile()?;
    let ay_source = fs::canonicalize(ay_source).map_err(|error| error.to_string())?;
    let ay_sha = sha256_file(&ay_source, "current behavior AY")?;
    let ay = stage_authenticated_executable(&ay_source, &ay_sha, "current behavior AY")?;
    let z3_source = reference_artifact_path(&profile.z3_overlay.reference_executable.path)?;
    let z3 = stage_authenticated_executable(
        &z3_source,
        &profile.z3_overlay.reference_executable.sha256,
        "current behavior Z3",
    )?;
    let resources = PlannedResources::plan(&locate_repo_root()?, 1, "current Z3 behavioral probes")
        .map_err(|error| error.to_string())?;
    let resource_envelope =
        effective_execution_envelope(&resources.plan, ENFORCEMENT_RSS_WATCHDOG_V1, timeout as f64)
            .map_err(|error| error.to_string())?;
    let coverage = coverage(&inventory)?;
    let mut results = Vec::new();
    for case in cases() {
        let reference_candidate = capture(
            &resources,
            &z3.path,
            &case.candidate,
            Provider::Z3,
            Duration::from_secs(timeout),
        )?;
        let reference_control = capture(
            &resources,
            &z3.path,
            &case.control,
            Provider::Z3,
            Duration::from_secs(timeout),
        )?;
        let ay_candidate = capture(
            &resources,
            &ay.path,
            &case.candidate,
            Provider::Ay,
            Duration::from_secs(timeout),
        )?;
        let ay_control = capture(
            &resources,
            &ay.path,
            &case.control,
            Provider::Ay,
            Duration::from_secs(timeout),
        )?;
        results.push(classify(
            &case,
            reference_candidate,
            reference_control,
            ay_candidate,
            ay_control,
        ));
    }
    if sha256_file(&ay.path, "post-run AY")? != ay_sha
        || sha256_file(&z3.path, "post-run Z3")? != profile.z3_overlay.reference_executable.sha256
        || sha256_file(&inventory_path, "post-run inventory")? != inventory_sha
    {
        return Err("behavior subject/reference/inventory changed during execution".to_string());
    }
    Ok(Report {
        schema: SCHEMA.to_string(),
        profile_id: PROFILE_ID.to_string(),
        profile_sha256: canonical_profile_sha256()?,
        inventory: Artifact {
            path: inventory_path.to_string_lossy().into_owned(),
            sha256: inventory_sha,
        },
        ay: Artifact {
            path: ay_source.to_string_lossy().into_owned(),
            sha256: ay_sha,
        },
        z3_sha256: profile.z3_overlay.reference_executable.sha256,
        timeout_seconds: timeout,
        resource_envelope,
        selected_checks_passed: results.iter().all(|row| row.passed),
        cases: results,
        coverage,
        full_semantics_complete: false,
    })
}

pub(super) fn run(args: &[String]) -> Result<i32, String> {
    if args
        .iter()
        .any(|arg| matches!(arg.as_str(), "--help" | "-h"))
    {
        println!("smtlib-conformance current-behavior --inventory FILE --ay FILE --out FILE [--timeout SECONDS]\n\nRun 15 fixed paired current-release semantic consumers under authenticated\nZ3 and staged AY. Untested catalog entries and full semantics remain explicit\ngaps. Exit zero means only these selected witnesses passed.");
        return Ok(0);
    }
    let mut inventory = None;
    let mut ay = None;
    let mut output = None;
    let mut timeout = 5u64;
    let mut iter = args.iter();
    while let Some(flag) = iter.next() {
        let value = iter.next().ok_or_else(|| format!("{flag} needs a value"))?;
        match flag.as_str() {
            "--inventory" => inventory = Some(PathBuf::from(value)),
            "--ay" => ay = Some(PathBuf::from(value)),
            "--out" => output = Some(PathBuf::from(value)),
            "--timeout" => {
                timeout = value
                    .parse()
                    .map_err(|_| "timeout must be integer seconds")?;
                if !(1..=60).contains(&timeout) {
                    return Err("timeout must be 1..60 seconds".to_string());
                }
            }
            _ => return Err(format!("unknown current-behavior option {flag}")),
        }
    }
    let output = output.ok_or("--out required")?;
    let report = collect(
        &inventory.ok_or("--inventory required")?,
        &ay.ok_or("--ay required")?,
        timeout,
    )?;
    atomic_write_new(&output, &pretty_json(&report)?)?;
    println!(
        "current_behavior={} selected_passed={}/{} full_semantics_complete=false",
        output.display(),
        report.cases.iter().filter(|row| row.passed).count(),
        report.cases.len()
    );
    Ok(i32::from(!report.selected_checks_passed))
}

pub(super) fn check(args: &[String]) -> Result<i32, String> {
    if args.len() != 1 {
        return Err("usage: current-behavior-check REPORT".to_string());
    }
    let bytes = read_bounded_bytes(
        Path::new(&args[0]),
        MAX_REPORT_BYTES,
        "current behavior report",
        true,
    )?;
    let report: Report = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    if report.schema != SCHEMA
        || report.profile_id != PROFILE_ID
        || report.profile_sha256 != canonical_profile_sha256()?
        || report.full_semantics_complete
        || !(1..=60).contains(&report.timeout_seconds)
        || report
            .cases
            .iter()
            .map(|row| row.case.clone())
            .collect::<Vec<_>>()
            != cases()
        || sha256_file(
            Path::new(&report.inventory.path),
            "current behavior inventory",
        )? != report.inventory.sha256
        || sha256_file(Path::new(&report.ay.path), "current behavior AY")? != report.ay.sha256
    {
        return Err("current behavior report has changed scope, inputs or identity".to_string());
    }
    let current = collect(
        Path::new(&report.inventory.path),
        Path::new(&report.ay.path),
        report.timeout_seconds,
    )?;
    if report != current {
        return Err("current behavior report differs from fresh live replay".to_string());
    }
    println!(
        "current_behavior_replay=PASS selected_checks_passed={} full_semantics_complete=false",
        report.selected_checks_passed
    );
    Ok(i32::from(!report.selected_checks_passed))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn normalization_does_not_erase_payload_or_atom_differences() {
        assert_eq!(
            normalized("( x\n 1 )").unwrap(),
            normalized("(x 1)").unwrap()
        );
        assert_ne!(normalized("(x 1)").unwrap(), normalized("(x1)").unwrap());
        assert_ne!(
            normalized("(echo \"a b\")").unwrap(),
            normalized("(echo \"a  b\")").unwrap()
        );
        assert_ne!(
            normalized("(x 0.33?)").unwrap(),
            normalized("(x 0.33)").unwrap()
        );
    }
    #[test]
    fn goal_depth_is_not_a_transform_witness() {
        let a = "(goals (goal (= x 1) :precision precise :depth 0))";
        let b = "(goals (goal (= x 1) :precision precise :depth 1))";
        assert_eq!(goal_payload(a).unwrap(), goal_payload(b).unwrap());
        assert_ne!(
            goal_payload(a).unwrap(),
            goal_payload("(goals (goal (= (+ x 0) 1) :depth 0))").unwrap()
        );
    }
    #[test]
    fn all_current_cases_have_owned_catalog_names_and_distinct_inputs() {
        let cases = cases();
        assert_eq!(cases.len(), 15);
        let ids = cases.iter().map(|case| &case.id).collect::<BTreeSet<_>>();
        assert_eq!(ids.len(), cases.len());
        for case in cases {
            assert_ne!(case.candidate, case.control);
            assert_ne!(case.scope.as_str(), "");
        }
    }
}
