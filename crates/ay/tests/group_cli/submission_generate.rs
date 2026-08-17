// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::path::Path;
use std::process::Command;

use tempfile::tempdir;

use serde_json::{json, Value};
#[cfg(unix)]
use sha2::{Digest, Sha256};
#[cfg(unix)]
use std::fs;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
#[cfg(unix)]
use std::sync::{Mutex, MutexGuard};

/// Serial guard for the two tests that build a real CHC package and then run the
/// real `ay --chc` solver against a benchmark smoke. Each such test spawns the
/// solver as a subprocess with an internal timeout derived from
/// `--benchmark-timeout-ms`. When the whole `group_cli` binary runs in parallel,
/// these two are the heaviest tests in this file; running them concurrently
/// piles two simultaneous packaging + solve workloads onto an already-saturated
/// machine, and the trivial CHC solve can miss its derived internal deadline and
/// degrade to `unknown` instead of the asserted `sat`. They pass in isolation
/// and only flake under contention, so serialize them against each other; the
/// assertions are unchanged.
#[cfg(unix)]
static CHC_SOLVER_SMOKE_SERIAL: Mutex<()> = Mutex::new(());

/// Acquire the CHC solver smoke serial guard, recovering from a poisoned lock so
/// one panicking test does not cascade into spurious failures in the other.
#[cfg(unix)]
fn chc_solver_smoke_guard() -> MutexGuard<'static, ()> {
    CHC_SOLVER_SMOKE_SERIAL
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

#[cfg(unix)]
const CHC_TEST_ALL_TRACKS: [&str; 11] = [
    "BOOL",
    "BV",
    "BV-Lin",
    "LRA-Lin",
    "LIA-Lin",
    "LIA",
    "LIA-Arrays",
    "LIA-Lin-Arrays",
    "ADT-LIA",
    "ADT-LIA-Arrays",
    "mixed_LIA_LRA",
];

fn assert_command_success(output: &std::process::Output, action: &str) {
    assert!(
        output.status.success(),
        "{action} should succeed; stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn chc_zenodo_submit_help_exposes_golden_path_only() {
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "submit", "chc-comp-zenodo", "--help"])
        .output()
        .expect("spawn ay submission submit chc-comp-zenodo --help");
    assert_command_success(&output, "CHC Zenodo submit help");
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(stdout.contains("Usage: ay submission submit chc-comp-zenodo [OPTIONS]"));
    assert!(stdout.contains("--dry-run"));
    assert!(stdout.contains("--skip-pr"));
    assert!(stdout.contains("--skip-build"));
    assert!(stdout.contains("--ay-bin"));
    assert!(
        !stdout.contains("--execute"),
        "submit help must use standard --dry-run convention:\n{stdout}"
    );
    assert!(
        !stdout.contains("GITHUB_OWNER"),
        "CHC-COMP 2026 owner is fixed by policy and should not be an operator argument:\n{stdout}"
    );
    assert!(
        !stdout.contains("--archive-url"),
        "non-golden archive reuse must stay out of normal help:\n{stdout}"
    );
}

#[cfg(unix)]
fn assert_file_exists(path: impl AsRef<Path>) {
    let path = path.as_ref();
    assert!(path.is_file(), "expected file {}", path.display());
}

fn assert_archive_member_modes(archive: impl AsRef<Path>, expected: &[(&str, &str)]) {
    let archive = archive.as_ref();
    let mut command = tar_command();
    command.arg("-tvzf").arg(archive);
    let output = command.output().expect("list submission archive");
    assert_command_success(&output, "tar list");
    let stdout = String::from_utf8_lossy(&output.stdout);
    for (member, mode) in expected {
        let actual = archive_member_mode(&stdout, member)
            .unwrap_or_else(|| panic!("archive member {member} missing in:\n{stdout}"));
        assert_eq!(
            actual,
            *mode,
            "archive member {member} in {} should have mode {mode}; listing:\n{stdout}",
            archive.display()
        );
    }
}

fn archive_member_mode(listing: &str, member: &str) -> Option<String> {
    listing.lines().find_map(|line| {
        let mut fields = line.split_whitespace();
        let mode = fields.next()?;
        let path = fields.last()?;
        (normalize_archive_member(path) == member).then(|| mode.to_string())
    })
}

fn normalize_archive_member(path: &str) -> String {
    let path = path.trim_start_matches("./").trim_end_matches('/');
    if path.is_empty() {
        ".".to_string()
    } else {
        path.to_string()
    }
}

fn tar_command() -> Command {
    #[cfg(windows)]
    {
        let mut command = Command::new(r"C:\msys64\usr\bin\tar.exe");
        command
            .arg("--force-local")
            .env("PATH", windows_submission_tool_path());
        command
    }
    #[cfg(not(windows))]
    {
        Command::new("tar")
    }
}

#[cfg(unix)]
fn workspace_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("crates/ay has a workspace root")
}

#[cfg(unix)]
fn write_minimal_chc_comp_root(root: &Path, tracks: &[&str], smt2: &str) {
    let smoke_dir = root.join("smoke");
    fs::create_dir_all(&smoke_dir).expect("create CHC smoke dir");
    for track in tracks {
        let set_file = chc_test_track_set_file(track);
        let stem = track.replace('-', "_");
        fs::write(
            root.join(format!("{set_file}.set")),
            format!("./smoke/{stem}.yml\n"),
        )
        .unwrap_or_else(|err| panic!("write {set_file}.set: {err}"));
        fs::write(
            smoke_dir.join(format!("{stem}.yml")),
            format!(
                "format_version: '2.0'\n\
                 input_files: {stem}.smt2\n\
                 properties:\n\
                 - expected_verdict: true\n\
                 majority_vote_verdict: sat\n\
                 property_file: ../properties/check-sat.prp\n"
            ),
        )
        .unwrap_or_else(|err| panic!("write {track} yml: {err}"));
        fs::write(smoke_dir.join(format!("{stem}.smt2")), smt2)
            .unwrap_or_else(|err| panic!("write {track} smt2: {err}"));
    }
    fs::create_dir_all(root.join("properties")).expect("create CHC properties dir");
    fs::write(root.join("properties/check-sat.prp"), "CHECK( sat )\n").expect("write CHC property");
}

#[cfg(unix)]
fn chc_test_track_set_file(track: &str) -> &str {
    match track {
        "BOOL" => "BOOL",
        "BV" => "BV",
        "BV-Lin" => "BV-Lin",
        "LRA-Lin" => "LRA-Lin",
        "LIA-Lin" => "LIA-Lin",
        "LIA" => "LIA",
        "LIA-Arrays" => "LIA-Arrays",
        "LIA-Lin-Arrays" => "LIA-Lin-Arrays",
        "ADT-LIA" => "ADT-LIA",
        "ADT-LIA-Arrays" => "ADT-LIA-Arrays",
        "mixed_LIA_LRA" => "mixed_LIA_LRA",
        other => panic!("unexpected CHC test track {other}"),
    }
}

#[cfg(unix)]
fn trivial_sat_chc() -> &'static str {
    "(set-logic HORN)\n\
     (set-info :status sat)\n\
     (declare-fun Inv (Int) Bool)\n\
     (assert (forall ((x Int)) (=> (= x 0) (Inv x))))\n\
     (assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))\n\
     (check-sat)\n"
}

#[cfg(unix)]
fn write_fake_linux_x86_64_binary(path: impl AsRef<Path>) {
    let path = path.as_ref();
    let mut bytes = vec![0_u8; 64];
    bytes[0..4].copy_from_slice(b"\x7fELF");
    bytes[4] = 2;
    bytes[5] = 1;
    bytes[18] = 0x3e;
    fs::write(path, bytes)
        .unwrap_or_else(|err| panic!("write fake Linux x86_64 binary {}: {err}", path.display()));
    fs::set_permissions(path, fs::Permissions::from_mode(0o755))
        .unwrap_or_else(|err| panic!("chmod fake Linux x86_64 binary {}: {err}", path.display()));
}

#[cfg(unix)]
fn generate_sat_submission(output_dir: &Path) {
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "generate", "sat", "--output"])
        .arg(output_dir)
        .output()
        .expect("run ay submission generate sat");
    assert_command_success(&output, "generate SAT submission");
}

#[cfg(unix)]
fn write_sat_env_probe_ay(sat_dir: &Path) {
    let ay = sat_dir.join("ay");
    fs::write(
        &ay,
        concat!(
            r#"#!/usr/bin/env bash
set -euo pipefail
printf 'authority=%s\n' "${"#,
            r#"AY_SAT_FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY-unset}"
printf 'current=%s\n' "${"#,
            r#"AY_SAT_FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT-unset}"
printf 'preflight=%s\n' "${"#,
            r#"AY_SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE-unset}"
printf 'matrix=%s\n' "${"#,
            r#"AY_SATCOMP_MATRIX-unset}"
printf 's UNKNOWN\n'
"#,
        ),
    )
    .expect("write SAT env probe ay");
    fs::set_permissions(&ay, fs::Permissions::from_mode(0o755)).expect("chmod SAT env probe ay");
}

#[cfg(unix)]
fn copy_chc_archive_payload(package_dir: &Path, staging_dir: &Path) -> std::path::PathBuf {
    let archive_root = staging_dir.join("ay");
    fs::create_dir_all(&archive_root).expect("create CHC archive staging dir");
    for member in ["ay", "run_solver.sh", "README.md", "LICENSE"] {
        fs::copy(
            package_dir.join("tool-archive/ay").join(member),
            archive_root.join(member),
        )
        .unwrap_or_else(|err| panic!("copy CHC archive member {member}: {err}"));
    }
    fs::set_permissions(archive_root.join("ay"), fs::Permissions::from_mode(0o755))
        .expect("chmod staged CHC ay");
    fs::set_permissions(
        archive_root.join("run_solver.sh"),
        fs::Permissions::from_mode(0o755),
    )
    .expect("chmod staged CHC run_solver.sh");
    archive_root
}

#[cfg(unix)]
fn rewrite_chc_archive(package_dir: &Path, staging_dir: &Path) {
    let chc_archive = package_dir.join("ay-chccomp-2026-linux-x86_64.tar.gz");
    fs::remove_file(&chc_archive).expect("remove original CHC archive");
    let mut tar = tar_command();
    let archive_output = tar
        .arg("-czf")
        .arg(&chc_archive)
        .arg("-C")
        .arg(staging_dir)
        .arg("ay")
        .output()
        .expect("rewrite CHC archive");
    assert_command_success(&archive_output, "rewrite CHC archive");
}

#[cfg(unix)]
fn test_sha256_file(path: impl AsRef<Path>) -> String {
    let bytes = fs::read(path.as_ref())
        .unwrap_or_else(|err| panic!("read {} for sha256: {err}", path.as_ref().display()));
    let digest = Sha256::digest(&bytes);
    let mut out = String::with_capacity(digest.len() * 2);
    for byte in digest {
        use std::fmt::Write as _;
        write!(&mut out, "{byte:02x}").expect("write sha256 hex");
    }
    out
}

#[cfg(unix)]
fn update_chc_manifest_archive_sha(package_dir: &Path, sha256: &str) {
    let manifest_path = package_dir.join("MANIFEST.json");
    let mut manifest: Value = serde_json::from_str(
        &fs::read_to_string(&manifest_path).expect("read CHC package manifest"),
    )
    .expect("manifest JSON parses");
    manifest["archive"]["sha256"] = Value::String(sha256.to_string());
    fs::write(
        &manifest_path,
        format!(
            "{}\n",
            serde_json::to_string_pretty(&manifest).expect("serialize CHC package manifest")
        ),
    )
    .expect("write CHC package manifest");
}

#[cfg(windows)]
fn windows_submission_tool_path() -> String {
    let current = std::env::var("PATH").unwrap_or_default();
    format!(r"C:\msys64\usr\bin;C:\msys64\ucrt64\bin;{current}")
}

#[cfg(windows)]
fn windows_submission_toolchain_available() -> bool {
    Path::new(r"C:\msys64\usr\bin\tar.exe").is_file()
        && Path::new(r"C:\msys64\usr\bin\gzip.exe").is_file()
        && Path::new(r"C:\msys64\usr\bin\bash.exe").is_file()
        && Path::new(r"C:\msys64\usr\bin\python3.exe").is_file()
        && Path::new(r"C:\msys64\usr\bin\xmllint.exe").is_file()
}

#[cfg(windows)]
fn ay_submission_command(ay_bin: &str) -> Command {
    // B41: --gzip is a CLI arg on the submission surface; callers append it
    // after the subcommand (global = true).
    let mut command = Command::new(ay_bin);
    command
        .env("PATH", windows_submission_tool_path())
        .args(["--gzip", r"C:\msys64\usr\bin\gzip.exe"]);
    command
}

#[test]
#[cfg(unix)]
fn submission_generate_all_writes_competition_skeletons() {
    let temp = tempdir().expect("temp dir");
    let out_dir = temp.path().join("submissions");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "generate", "all", "--output"])
        .arg(&out_dir)
        .output()
        .expect("run ay submission generator");
    assert_command_success(&output, "generator");
    let generator_stdout = String::from_utf8_lossy(&output.stdout);
    assert!(generator_stdout
        .contains("track-model official_chc_comp_2026_tracks=9 local_set_file_categories=11"));
    assert!(generator_stdout.contains("BV=BV-Nonlin"));

    let sat_run = fs::read_to_string(out_dir.join("sat-comp-2026/run.sh")).expect("SAT run.sh");
    assert!(sat_run.contains("--proof-format drat"));
    assert!(sat_run.contains("proof.out"));
    assert!(sat_run.contains("STAREXEC_WALLCLOCK_LIMIT"));
    assert!(sat_run.contains("SOLVER_ARGS+=(--timeout \"$TIMEOUT_MS\")"));
    assert!(sat_run.contains("-u AY_SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE"));
    assert!(sat_run.contains("-u AY_SAT_FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY"));
    assert!(sat_run.contains("-u AY_SAT_FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT"));

    let chc_xml = fs::read_to_string(out_dir.join("chc-comp-2026/benchmark-defs/ay.xml.template"))
        .expect("CHC XML");
    assert!(chc_xml.contains("<rundefinition name=\"CHC-COMP2026_check-sat\">"));
    for track in [
        "BOOL",
        "BV",
        "BV-Lin",
        "LRA-Lin",
        "LIA-Lin",
        "LIA",
        "LIA-Arrays",
        "LIA-Lin-Arrays",
        "ADT-LIA",
        "ADT-LIA-Arrays",
        "mixed_LIA_LRA",
    ] {
        assert!(
            chc_xml.contains(&format!(r#"<tasks name="{track}">"#)),
            "CHC XML must include current set-file category task {track}"
        );
        assert!(
            chc_xml.contains(&format!(
                "<includesfile>../chc-comp26-benchmarks/{track}.set</includesfile>"
            )),
            "CHC XML must include current set-file category {track}"
        );
    }
    for unavailable_track in ["BV-Nonlin", "LIA-Nonlin", "LIA-Nonlin-Arrays"] {
        assert!(
            !chc_xml.contains(&format!(
                "<includesfile>../chc-comp26-benchmarks/{unavailable_track}.set</includesfile>"
            )),
            "CHC XML must not include unavailable track alias {unavailable_track}"
        );
    }
    let chc_readme =
        fs::read_to_string(out_dir.join("chc-comp-2026/README-CHC-PR.md")).expect("CHC README");
    assert!(chc_readme.contains("Current generated local set-file categories:"));
    assert!(chc_readme.contains("Official CHC-COMP 2026 planned tracks: 9"));
    assert!(chc_readme.contains("Local chc-comp26 set-file categories used by this CLI: 11"));
    assert!(chc_readme.contains("| `BV` | `BV-Nonlin` | `official-track-alias` |"));
    assert!(chc_readme.contains("| `LIA` | `LIA-Nonlin` | `official-track-alias` |"));
    assert!(chc_readme.contains("| `BOOL` | `none` | `internal-smoke-category` |"));

    let smt_json_text =
        fs::read_to_string(out_dir.join("smt-comp-2026/ay-smt-comp-2026.json")).expect("SMT JSON");
    let smt_json: Value = serde_json::from_str(&smt_json_text).expect("SMT JSON parses");
    assert_eq!(smt_json["solver_type"], "Standalone");
    assert_eq!(smt_json["contributors"][0]["name"], "Andrew Yates");
    assert_eq!(
        smt_json["contacts"][0]["email"],
        "andrewyates.name@gmail.com"
    );
    assert!(smt_json["system_description"]
        .as_str()
        .expect("system_description is URI string")
        .starts_with("https://zenodo.org/"));
    assert_eq!(smt_json["command"][0], "run_solver.sh");
    assert!(
        !smt_json
            .as_object()
            .expect("root object")
            .keys()
            .any(|key| key.starts_with('_')),
        "SMT-COMP JSON must not contain schema-invalid note fields: {smt_json_text}"
    );

    let pb_dir = out_dir.join("pb-comp-2026");
    let pb_commands = fs::read_to_string(pb_dir.join("COMMAND-LINES.txt"))
        .expect("generated PB command lines should be readable");
    assert!(
        pb_commands.contains("DIR/run_solver.sh BENCHNAME PROOFFILE"),
        "PB-COMP certified command line must use the PROOFFILE placeholder as an argv value: {pb_commands}"
    );
    fs::copy(env!("CARGO_BIN_EXE_ay"), pb_dir.join("ay")).expect("copy ay into PB skeleton");
    let proof_path = pb_dir.join("smoke.veripb");
    let pb_output = Command::new(pb_dir.join("run_solver.sh"))
        .arg(pb_dir.join("smoke.opb"))
        .arg(&proof_path)
        .env("TIMELIMIT", "1")
        .output()
        .expect("run generated PB wrapper");
    assert_eq!(
        pb_output.status.code(),
        Some(30),
        "PB wrapper should report OPTIMUM FOUND; stdout={} stderr={}",
        String::from_utf8_lossy(&pb_output.stdout),
        String::from_utf8_lossy(&pb_output.stderr)
    );
    let proof = fs::read_to_string(&proof_path).expect("PB proof");
    // VeriPB 3.0.2 (unchecked-deletion mode) rejects un-hinted finite bounds, so
    // `conclusion BOUNDS` now carries a lower-bound contradiction-row hint and an
    // inline incumbent witness (see 8d3124e4): `BOUNDS <lb> : <id> <ub> : <sol>`.
    // Assert the proven optimum of 1 with both hints, tolerating the hint id.
    assert!(
        proof.contains("conclusion BOUNDS 1 : ") && proof.contains(" 1 : x1;"),
        "PB proof must conclude a hinted optimum bound of 1: {proof}"
    );
}

#[test]
#[cfg(unix)]
fn generated_sat_run_sh_scrubs_stale_fmla_authority_env() {
    let temp = tempdir().expect("temp dir");
    let sat_dir = temp.path().join("sat");
    generate_sat_submission(&sat_dir);
    write_sat_env_probe_ay(&sat_dir);

    let bench = temp.path().join("bench.cnf");
    let proof_dir = temp.path().join("proof");
    let stale_replay = temp.path().join("stale-replay.json");
    fs::write(&bench, "p cnf 1 0\n").expect("write SAT bench");
    fs::write(&stale_replay, "{}\n").expect("write stale replay artifact");

    let output = Command::new(sat_dir.join("run.sh"))
        .arg(&bench)
        .arg(&proof_dir)
        .env("AY_SATCOMP_MATRIX", "1")
        .env(
            "AY_SAT_FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY",
            &stale_replay,
        )
        .env(
            "AY_SAT_FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT",
            temp.path().join("other-proof.out"),
        )
        .env("AY_SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE", "1")
        .output()
        .expect("run generated SAT wrapper with stale Fmla env");
    assert_command_success(&output, "generated SAT wrapper stale-env scrub");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("authority=unset\n"),
        "stale Fmla authority replay env must be scrubbed: {stdout}"
    );
    assert!(
        stdout.contains("current=unset\n"),
        "stale Fmla current proof env must be scrubbed: {stdout}"
    );
    assert!(
        stdout.contains("preflight=unset\n"),
        "Fmla preflight route env must be scrubbed: {stdout}"
    );
}

#[test]
#[cfg(unix)]
fn generated_sat_run_sh_allows_matrix_two_pass_fmla_authority_env() {
    let temp = tempdir().expect("temp dir");
    let sat_dir = temp.path().join("sat");
    generate_sat_submission(&sat_dir);
    write_sat_env_probe_ay(&sat_dir);

    let bench = temp.path().join("bench.cnf");
    let proof_dir = temp.path().join("proof");
    let proof_file = proof_dir.join("proof.out");
    let replay = temp
        .path()
        .join("fmla-main-lrat-postcheck-admission-replay.json");
    fs::write(&bench, "p cnf 1 0\n").expect("write SAT bench");
    fs::write(&replay, "{}\n").expect("write replay artifact marker");

    let output = Command::new(sat_dir.join("run.sh"))
        .arg(&bench)
        .arg(&proof_dir)
        .env("AY_SATCOMP_MATRIX", "1")
        .env(
            "AY_SAT_FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY",
            &replay,
        )
        .env("AY_SAT_FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT", &proof_file)
        .env("AY_SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE", "1")
        .output()
        .expect("run generated SAT wrapper with matrix Fmla handoff");
    assert_command_success(&output, "generated SAT wrapper matrix Fmla handoff");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains(&format!("authority={}\n", replay.display())),
        "matrix two-pass replay env must reach ay: {stdout}"
    );
    assert!(
        stdout.contains(&format!("current={}\n", proof_file.display())),
        "matrix two-pass current proof env must reach ay: {stdout}"
    );
    assert!(
        stdout.contains("preflight=unset\n"),
        "Fmla preflight route env must still be scrubbed: {stdout}"
    );
    assert!(
        stdout.contains("matrix=1\n"),
        "matrix marker should remain visible to the probe: {stdout}"
    );
}

#[test]
#[cfg(unix)]
fn sat_matrix_retains_fmla_dry_run_artifact_for_unknown_timeout_route() {
    let temp = tempdir().expect("temp dir");
    let solver_root = temp.path().join("solver");
    let output_dir = temp.path().join("matrix");
    fs::create_dir_all(&solver_root).expect("create fake solver root");
    let run_sh = solver_root.join("run.sh");
    fs::write(
        &run_sh,
        concat!(
            r#"#!/usr/bin/env bash
set -euo pipefail

artifact="${"#,
            r#"AY_SAT_FMLA_LEARNED_LRAT_DRY_RUN_ARTIFACT:-}"
if [[ -n "$artifact" ]]; then
  mkdir -p "$(dirname "$artifact")"
  cat > "$artifact" <<'JSON'
{"schema":"ay.fmla-learned-lrat-dry-run-proof-artifact/v1","authorizes_main_proof_out":false,"materialization_status":"fail_closed_no_learned_lrat_authority_records"}
JSON
fi
printf 's UNKNOWN\n'
printf 'c timeout\n' >&2
"#,
        ),
    )
    .expect("write fake SAT wrapper");
    fs::set_permissions(&run_sh, fs::Permissions::from_mode(0o755))
        .expect("chmod fake SAT wrapper");

    let input = temp.path().join("FmlaEquivChain_4_6_6.cnf");
    fs::write(&input, "p cnf 1 1\n1 0\n").expect("write Fmla marker CNF");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args([
            "submission",
            "preflight",
            "sat-matrix",
            "run",
            "--suite",
            "local",
            "--run-sh",
        ])
        .arg(&run_sh)
        .args(["--output"])
        .arg(&output_dir)
        .args(["--instance"])
        .arg(&input)
        .args(["--expected", "unknown", "--timeout-sec", "60"])
        .output()
        .expect("run SAT matrix with fake timeout wrapper");
    assert_command_success(&output, "SAT matrix fake Fmla timeout route");

    let raw = fs::read_to_string(output_dir.join("default-raw.tsv")).expect("read raw TSV");
    let mut lines = raw.lines();
    let headers: Vec<&str> = lines.next().expect("raw TSV header").split('\t').collect();
    let cells: Vec<&str> = lines.next().expect("raw TSV row").split('\t').collect();
    let get = |field: &str| -> &str {
        let index = headers
            .iter()
            .position(|header| *header == field)
            .unwrap_or_else(|| panic!("missing raw TSV field {field}: {raw}"));
        cells.get(index).copied().unwrap_or("")
    };

    assert_eq!(get("actual"), "unknown");
    assert_eq!(get("proof_bytes"), "0");
    assert_ne!(get("proof_status"), "valid");
    let artifact = get("fmla_learned_lrat_dry_run_artifact");
    assert!(
        !artifact.is_empty(),
        "Fmla dry-run artifact path should be retained in raw TSV: {raw}"
    );
    assert_file_exists(artifact);
    assert_eq!(
        get("fmla_learned_lrat_dry_run_artifact_sha256"),
        test_sha256_file(artifact)
    );
    assert_eq!(
        get("fmla_learned_lrat_dry_run_artifact_schema"),
        "ay.fmla-learned-lrat-dry-run-proof-artifact/v1"
    );
    assert!(
        get("fmla_main_lrat_authority_replay_env").is_empty(),
        "UNKNOWN route must not advertise a Main/LRAT authority replay env handoff: {raw}"
    );
    assert!(
        get("fmla_main_lrat_authority_replay_env_value").is_empty(),
        "UNKNOWN route must not advertise a Main/LRAT authority replay path: {raw}"
    );
    let artifact_json: Value =
        serde_json::from_str(&fs::read_to_string(artifact).expect("read retained artifact"))
            .expect("parse retained artifact");
    assert_eq!(artifact_json["authorizes_main_proof_out"], false);
}

#[test]
#[cfg(unix)]
fn sat_matrix_two_pass_fmla_rejects_invalid_authority_handoff() {
    let temp = tempdir().expect("temp dir");
    let solver_root = temp.path().join("solver");
    let output_dir = temp.path().join("matrix");
    fs::create_dir_all(&solver_root).expect("create fake solver root");

    let run_sh = solver_root.join("run.sh");
    fs::write(
        &run_sh,
        r#"#!/usr/bin/env bash
set -euo pipefail
input="$1"
proof_dir="$2"
mkdir -p "$proof_dir"
cat > "$proof_dir/proof.out" <<'EOF'
c fake checked proof
1 0
EOF
printf '{"sat.decompose_lrat_preflight_main_rewrite_materializer_attempts":1,"sat.decompose_lrat_preflight_main_rewrite_materializer_proof_emit_records_seen":1,"sat.decompose_lrat_preflight_main_rewrite_materializer_records":1,"sat.decompose_lrat_preflight_main_rewrite_materializer_fail_closed":1,"sat.decompose_lrat_preflight_main_rewrite_materializer_missing_runtime_records":0,"sat.preprocess_tx_fail_closed":1,"sat.preprocess_tx_committed":0,"input":"%s"}\n' "$input" >&2
printf 's UNSATISFIABLE\n'
"#,
    )
    .expect("write fake SAT wrapper");
    fs::set_permissions(&run_sh, fs::Permissions::from_mode(0o755))
        .expect("chmod fake SAT wrapper");

    let ay = solver_root.join("ay");
    fs::write(
        &ay,
        r#"#!/usr/bin/env python3
import hashlib
import json
import os
import sys

args = sys.argv[1:]
if args[:2] == ["check", "lrat"]:
    sys.exit(0)
if args[:2] != ["check", "fmla-postcheck-admission"]:
    sys.exit(2)

def value_after(flag):
    return args[args.index(flag) + 1]

replay_artifact = value_after("--replay-artifact")
summary_tsv = value_after("--summary-tsv")
proof_out = value_after("--proof-out")
external_artifact = value_after("--external-checker-artifact")
external_artifact_sha256 = value_after("--external-checker-artifact-sha256")
with open(proof_out, "rb") as handle:
    proof_sha = hashlib.sha256(handle.read()).hexdigest()
with open(external_artifact, "r", encoding="utf-8") as handle:
    checker_artifact = json.load(handle)
payload = {
    "schema": "ay.fmla-main-lrat-postcheck-admission-replay/v1",
    "status": "committed_checker_backed_admission",
    "proof_obligation_rows": 1,
    "external_proof_checker_verdict_artifact_rows": 0,
    "external_proof_checker_verdict_artifact": external_artifact,
    "external_proof_checker_verdict_artifact_sha256": external_artifact_sha256,
    "external_proof_checker_verdict_artifact_schema": "ay.fmla-main-lrat-external-checker-verdict/v1",
    "external_proof_checker_verdict_artifact_runtime_field": "external_proof_checker_verdict_artifact",
    "learned_lrat_main_proof_authority_status": "authorized",
    "learned_lrat_main_proof_authority_external_checker_verified": True,
    "learned_lrat_main_proof_authority_proof_out_contains_lrat_fragment": True,
    "learned_lrat_main_proof_authority_authorizes_main_proof_out": True,
    "external_proof_checker_verdict": "VERIFIED_UNSAT",
    "external_proof_checker_path": checker_artifact["checker_path"],
    "external_proof_checker_sha256": checker_artifact["checker_sha256"],
    "external_proof_checker_command": checker_artifact["checker_command"],
    "external_proof_checker_argv": checker_artifact["checker_argv"],
    "external_proof_checker_dimacs_path": checker_artifact["checked_dimacs_path"],
    "external_proof_checker_dimacs_sha256": checker_artifact["checked_dimacs_sha256"],
    "checker_exit_code": 0,
    "learned_lrat_main_proof_authority_proof_out_path": proof_out,
    "learned_lrat_main_proof_authority_proof_out_sha256": proof_sha,
}
os.makedirs(os.path.dirname(replay_artifact), exist_ok=True)
with open(replay_artifact, "w", encoding="utf-8") as handle:
    handle.write(json.dumps(payload) + "\n")
with open(replay_artifact, "rb") as handle:
    replay_sha = hashlib.sha256(handle.read()).hexdigest()
with open(summary_tsv, "w", encoding="utf-8") as handle:
    handle.write(f"committed_checker_backed_admission\t{replay_artifact}\t{replay_sha}\t1\t0\t0\n")
print(json.dumps(payload))
"#,
    )
    .expect("write fake ay checker");
    fs::set_permissions(&ay, fs::Permissions::from_mode(0o755)).expect("chmod fake ay");

    let checker = temp.path().join("cake_lpr");
    fs::write(
        &checker,
        r#"#!/usr/bin/env bash
printf 's VERIFIED UNSAT\n'
"#,
    )
    .expect("write fake external checker");
    fs::set_permissions(&checker, fs::Permissions::from_mode(0o755))
        .expect("chmod fake external checker");

    let input = temp.path().join("FmlaEquivChain_4_6_6.cnf");
    fs::write(&input, "p cnf 1 2\n1 0\n-1 0\n").expect("write Fmla marker CNF");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args([
            "submission",
            "preflight",
            "sat-matrix",
            "run",
            "--suite",
            "local",
            "--run-sh",
        ])
        .arg(&run_sh)
        .args(["--output"])
        .arg(&output_dir)
        .args(["--instance"])
        .arg(&input)
        .args([
            "--expected",
            "unsat",
            "--timeout-sec",
            "1",
            "--proof-format",
            "lrat",
            "--proof-checker",
        ])
        .arg(&checker)
        .arg("--fmla-main-lrat-authority-replay-two-pass")
        .output()
        .expect("run SAT matrix with invalid Fmla authority handoff");

    assert!(
        !output.status.success(),
        "invalid Fmla authority handoff must fail closed; stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("valid Fmla Main/LRAT authority replay handoff required"),
        "unexpected stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn sat_matrix_two_pass_fmla_flag_rejects_non_lrat_configuration() {
    let temp = tempdir().expect("temp dir");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args([
            "submission",
            "preflight",
            "sat-matrix",
            "run",
            "--suite",
            "local",
            "--output",
        ])
        .arg(temp.path().join("matrix"))
        .arg("--fmla-main-lrat-authority-replay-two-pass")
        .output()
        .expect("run SAT matrix with two-pass flag under default DRAT proof format");

    assert!(
        !output.status.success(),
        "two-pass Fmla flag under non-LRAT configuration must fail closed; stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("valid Fmla Main/LRAT authority replay handoff required"),
        "unexpected stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[cfg(unix)]
fn submission_package_all_gates_and_writes_package_artifacts() {
    let temp = tempdir().expect("temp dir");
    let package_dir = temp.path().join("packages");
    let ay_bin = env!("CARGO_BIN_EXE_ay");

    let package_output = Command::new(ay_bin)
        .args(["submission", "package", "all", "--output"])
        .arg(&package_dir)
        .args(["--ay-bin", ay_bin])
        .output()
        .expect("run ay submission package all");
    assert_command_success(&package_output, "package all");
    let package_stderr = String::from_utf8_lossy(&package_output.stderr);
    assert!(
        package_stderr.contains("skipping PB-COMP generic package path"),
        "package all must not emit the non-authoritative generic PB package: {package_stderr}"
    );

    let gate_output = Command::new(ay_bin)
        .args(["submission", "gate", "all", "--package"])
        .arg(&package_dir)
        .output()
        .expect("run ay submission gate all");
    assert_command_success(&gate_output, "gate all");
    let gate_stdout = String::from_utf8_lossy(&gate_output.stdout);
    assert!(gate_stdout.contains("[OK] SAT-COMP gate"));
    assert!(gate_stdout.contains("[OK] CHC-COMP gate"));
    assert!(gate_stdout.contains("[PASS] CHC-COMP: CHC Python tooldef compiles"));
    assert!(!gate_stdout.contains("[OK] PB-COMP gate"));
    assert!(gate_stdout.contains("[OK] SMT-COMP gate"));
    let gate_stderr = String::from_utf8_lossy(&gate_output.stderr);
    assert!(
        gate_stderr.contains("skipping PB-COMP generic gate path"),
        "gate all must not bless the non-authoritative generic PB package: {gate_stderr}"
    );

    let sat_dir = package_dir.join("sat-comp-2026");
    assert_file_exists(sat_dir.join("repo/build.sh"));
    assert_file_exists(sat_dir.join("repo/run.sh"));
    assert_file_exists(sat_dir.join("repo/ay"));
    assert_file_exists(sat_dir.join("ay-sat-comp-2026.tar.gz"));
    assert_file_exists(sat_dir.join("MANIFEST.json"));

    let chc_dir = package_dir.join("chc-comp-2026");
    assert_file_exists(chc_dir.join("pr/Makefile.ay.fragment"));
    assert_file_exists(chc_dir.join("pr/benchmark-defs/ay.xml.template"));
    assert_file_exists(chc_dir.join("pr/tooldefs/ay.py"));
    assert_file_exists(chc_dir.join("tool-archive/ay/ay"));
    assert_file_exists(chc_dir.join("tool-archive/ay/run_solver.sh"));
    let chc_archive = chc_dir.join("ay-chccomp-2026-linux-x86_64.tar.gz");
    assert_file_exists(&chc_archive);
    assert_file_exists(chc_dir.join("MANIFEST.json"));
    assert_archive_member_modes(
        &chc_archive,
        &[
            ("ay", "drwxr-xr-x"),
            ("ay/README.md", "-rw-r--r--"),
            ("ay/run_solver.sh", "-rwxr-xr-x"),
            ("ay/ay", "-rwxr-xr-x"),
        ],
    );

    assert!(
        !package_dir.join("pb-comp-2026").exists(),
        "package all must not stage the non-authoritative generic PB package"
    );

    let smt_dir = package_dir.join("smt-comp-2026");
    assert_file_exists(smt_dir.join("package/run_solver.sh"));
    assert_file_exists(smt_dir.join("package/run_solver_mv.sh"));
    assert_file_exists(smt_dir.join("package/run_solver_incr.sh"));
    assert_file_exists(smt_dir.join("package/ay"));
    assert_file_exists(smt_dir.join("pr/ay-smt-comp-2026.json"));
    assert_file_exists(smt_dir.join("ay-smt-comp-2026.tar.gz"));
    assert_file_exists(smt_dir.join("MANIFEST.json"));
}

#[test]
#[cfg(unix)]
fn submission_package_pb_fails_closed_to_pb26_wrapper_path() {
    let temp = tempdir().expect("temp dir");
    let package_dir = temp.path().join("pb-package");
    let ay_bin = env!("CARGO_BIN_EXE_ay");

    let package_output = Command::new(ay_bin)
        .args(["submission", "package", "pb", "--output"])
        .arg(&package_dir)
        .args(["--ay-bin", ay_bin])
        .output()
        .expect("run ay submission package pb");
    assert!(
        !package_output.status.success(),
        "generic PB package path must fail closed; stdout={} stderr={}",
        String::from_utf8_lossy(&package_output.stdout),
        String::from_utf8_lossy(&package_output.stderr)
    );
    let package_stderr = String::from_utf8_lossy(&package_output.stderr);
    assert!(package_stderr.contains("PB-COMP generic submission packaging is disabled for PB26"));
    assert!(package_stderr.contains("competition/pb26/prepare_submission.sh --archive"));
    assert!(package_stderr.contains("scripts/check_pb26_submission.sh"));

    let gate_output = Command::new(ay_bin)
        .args(["submission", "gate", "pb", "--package"])
        .arg(&package_dir)
        .output()
        .expect("run ay submission gate pb");
    assert!(
        !gate_output.status.success(),
        "generic PB gate path must fail closed; stdout={} stderr={}",
        String::from_utf8_lossy(&gate_output.stdout),
        String::from_utf8_lossy(&gate_output.stderr)
    );
    let gate_stderr = String::from_utf8_lossy(&gate_output.stderr);
    assert!(gate_stderr.contains("PB-COMP generic submission packaging is disabled for PB26"));
    assert!(gate_stderr.contains("ay submission preflight pb-comp-verify"));
}

#[test]
#[cfg(unix)]
fn submission_gate_chc_require_linux_checks_archive_binary_when_tool_archive_differs() {
    let temp = tempdir().expect("temp dir");
    let package_dir = temp.path().join("chc-package");
    let ay_bin = env!("CARGO_BIN_EXE_ay");

    let package_output = Command::new(ay_bin)
        .args(["submission", "package", "chc", "--output"])
        .arg(&package_dir)
        .args(["--ay-bin", ay_bin])
        .output()
        .expect("run ay submission package chc");
    assert_command_success(&package_output, "package chc");

    write_fake_linux_x86_64_binary(package_dir.join("tool-archive/ay/ay"));

    let staging_dir = temp.path().join("bad-chc-archive");
    let archive_root = copy_chc_archive_payload(&package_dir, &staging_dir);
    let archived_ay = archive_root.join("ay");
    fs::write(&archived_ay, b"not a Linux ELF binary\n").expect("write divergent archived ay");
    fs::set_permissions(&archived_ay, fs::Permissions::from_mode(0o755))
        .expect("chmod divergent archived ay");

    rewrite_chc_archive(&package_dir, &staging_dir);

    let gate_output = Command::new(ay_bin)
        .args(["submission", "gate", "chc", "--package"])
        .arg(&package_dir)
        .args(["--require-linux", "--skip-smoke"])
        .output()
        .expect("run ay submission gate chc");

    assert!(
        !gate_output.status.success(),
        "CHC gate should reject non-Linux ay/ay inside archive; stdout={} stderr={}",
        String::from_utf8_lossy(&gate_output.stdout),
        String::from_utf8_lossy(&gate_output.stderr)
    );
    let stdout = String::from_utf8_lossy(&gate_output.stdout);
    assert!(
        stdout.contains("CHC archived ay binary: expected linux-elf-x86_64"),
        "CHC gate should report the archived binary failure; stdout={stdout}"
    );
}

#[test]
#[cfg(windows)]
fn submission_package_all_windows_skip_smoke_gates_and_writes_archive_modes() {
    if !windows_submission_toolchain_available() {
        eprintln!("skipping Windows submission package test: MSYS2 tools are unavailable");
        return;
    }

    let temp = tempdir().expect("temp dir");
    let package_dir = temp.path().join("packages");
    let ay_bin = env!("CARGO_BIN_EXE_ay");

    let package_output = ay_submission_command(ay_bin)
        .args(["submission", "package", "all", "--output"])
        .arg(&package_dir)
        .args(["--ay-bin", ay_bin])
        .output()
        .expect("run ay submission package all");
    assert_command_success(&package_output, "package all");
    let package_stderr = String::from_utf8_lossy(&package_output.stderr);
    assert!(
        package_stderr.contains("skipping PB-COMP generic package path"),
        "package all must not emit the non-authoritative generic PB package: {package_stderr}"
    );

    let gate_output = ay_submission_command(ay_bin)
        .args(["submission", "gate", "all", "--package"])
        .arg(&package_dir)
        .arg("--skip-smoke")
        .output()
        .expect("run ay submission gate all");
    assert_command_success(&gate_output, "gate all");
    let gate_stdout = String::from_utf8_lossy(&gate_output.stdout);
    assert!(gate_stdout.contains("[OK] SAT-COMP gate"));
    assert!(gate_stdout.contains("[OK] CHC-COMP gate"));
    assert!(gate_stdout.contains("[PASS] CHC-COMP: CHC Python tooldef compiles"));
    assert!(!gate_stdout.contains("[OK] PB-COMP gate"));
    assert!(gate_stdout.contains("[OK] SMT-COMP gate"));
    let gate_stderr = String::from_utf8_lossy(&gate_output.stderr);
    assert!(
        gate_stderr.contains("skipping PB-COMP generic gate path"),
        "gate all must not bless the non-authoritative generic PB package: {gate_stderr}"
    );

    assert_archive_member_modes(
        package_dir
            .join("chc-comp-2026")
            .join("ay-chccomp-2026-linux-x86_64.tar.gz"),
        &[
            ("ay", "drwxr-xr-x"),
            ("ay/README.md", "-rw-r--r--"),
            ("ay/run_solver.sh", "-rwxr-xr-x"),
            ("ay/ay", "-rwxr-xr-x"),
        ],
    );
}

#[test]
fn submission_preflight_chc_baseline_compare_fast_proxy_requires_timeout() {
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args([
            "submission",
            "preflight",
            "chc-baseline-compare",
            "--profile",
            "fast-proxy",
        ])
        .output()
        .expect("run CHC baseline compare without fast-proxy timeout");
    assert!(
        !output.status.success(),
        "fast-proxy without timeout must fail; stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("--profile fast-proxy requires --timeout-sec"));
}

#[test]
#[cfg(unix)]
fn submission_preflight_chc_baseline_compare_runs_same_timeout_evidence() {
    // The compare harness takes a host-wide non-blocking oom-guard lease;
    // serialize the two baseline-compare runs so they refuse concurrent
    // sweeps (the guard's job) without refusing each other.
    let _serial = chc_solver_smoke_guard();
    let temp = tempdir().expect("temp dir");
    let benchmark_root = temp.path().join("chc-bench");
    let baseline_path = temp.path().join("baseline.json");
    let output_dir = temp.path().join("evidence");
    let ay_stub = temp.path().join("ay-compare-stub");
    write_minimal_chc_comp_root(&benchmark_root, &["BV-Lin"], trivial_sat_chc());
    fs::write(
        &baseline_path,
        format!(
            "{}\n",
            serde_json::to_string_pretty(&json!({
                "suite": "test-chc-baseline",
                "benchmarks_dir": benchmark_root.display().to_string(),
                "timeout_sec": 2,
                "baseline_commit": "test-baseline",
                "baseline_date": "2026-05-04",
                "benchmarks_total": 1,
                "solved_total": 1,
                "benchmarks": [{
                    "file": "smoke/BV_Lin.smt2",
                    "status": "sat",
                    "elapsed_ms": 100,
                    "expected_status": "sat"
                }]
            }))
            .expect("serialize baseline")
        ),
    )
    .expect("write baseline");
    fs::write(
        &ay_stub,
        "#!/usr/bin/env bash\n\
         if [[ \"$*\" == *--version* ]]; then\n\
           printf 'ay compare stub\\n'\n\
           printf 'build.stamp=compare-stub\\n'\n\
           exit 0\n\
         fi\n\
         printf 'sat\\n'\n",
    )
    .expect("write ay compare stub");
    fs::set_permissions(&ay_stub, fs::Permissions::from_mode(0o755))
        .expect("chmod ay compare stub");

    // The same-timeout gate also requires the baseline's recorded resource
    // plan to match the current host's plan; that plan is host-specific, so
    // harvest it from a first (non-comparable, expected-fail) compare run and
    // embed it into the baseline before the gating run.
    let probe = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "preflight", "chc-baseline-compare"])
        .args(["--baseline"])
        .arg(&baseline_path)
        .args(["--bench-dir"])
        .arg(&benchmark_root)
        .args(["--ay"])
        .arg(&ay_stub)
        .args(["--output-dir"])
        .arg(&output_dir)
        .output()
        .expect("run CHC baseline compare resource-plan probe");
    assert!(
        !probe.status.success(),
        "compare without a recorded resource plan must be non-comparable and fail; stdout={} stderr={}",
        String::from_utf8_lossy(&probe.stdout),
        String::from_utf8_lossy(&probe.stderr)
    );
    let probe_payload: Value = serde_json::from_str(
        &fs::read_to_string(output_dir.join("chc-baseline-compare.json"))
            .expect("probe evidence JSON"),
    )
    .expect("probe evidence JSON parses");
    assert_eq!(
        probe_payload["summary"]["non_comparable_baseline"], 1,
        "probe run must fail solely on baseline comparability: {probe_payload}"
    );
    let resource_plan = probe_payload["resource_plan"].clone();
    assert!(
        resource_plan.is_object(),
        "probe evidence must record the host resource plan: {probe_payload}"
    );
    let mut baseline: Value = serde_json::from_str(
        &fs::read_to_string(&baseline_path).expect("read baseline for plan embedding"),
    )
    .expect("baseline JSON parses");
    baseline["resource_plan"] = resource_plan;
    fs::write(
        &baseline_path,
        format!(
            "{}\n",
            serde_json::to_string_pretty(&baseline).expect("serialize comparable baseline")
        ),
    )
    .expect("rewrite baseline with host resource plan");

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "preflight", "chc-baseline-compare"])
        .args(["--baseline"])
        .arg(&baseline_path)
        .args(["--bench-dir"])
        .arg(&benchmark_root)
        .args(["--ay"])
        .arg(&ay_stub)
        .args(["--output-dir"])
        .arg(&output_dir)
        .output()
        .expect("run CHC baseline compare through Rust CLI");
    assert_command_success(&output, "CHC baseline compare");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("status=pass evidence=chc-baseline-compare"));
    assert!(stdout.contains("profile=same-timeout"));
    assert!(stdout.contains("run_type=same-timeout-gate"));
    assert!(stdout.contains("direct_regressions=0"));

    let payload_text =
        fs::read_to_string(output_dir.join("chc-baseline-compare.json")).expect("evidence JSON");
    let payload: Value = serde_json::from_str(&payload_text).expect("evidence JSON parses");
    assert_eq!(
        payload["run_classification"]["run_type"],
        "same-timeout-gate"
    );
    assert_eq!(payload["summary"]["current_solved_checked"], 1);
    assert_eq!(payload["summary"]["direct_regressions"], 0);
    assert!(output_dir.join("chc-baseline-compare.csv").is_file());
}

#[test]
#[cfg(unix)]
fn submission_preflight_chc_baseline_compare_direct_regression_reports_fail() {
    // See submission_preflight_chc_baseline_compare_runs_same_timeout_evidence:
    // serialized against the shared host-wide oom-guard lease.
    let _serial = chc_solver_smoke_guard();
    let temp = tempdir().expect("temp dir");
    let benchmark_root = temp.path().join("chc-bench");
    let baseline_path = temp.path().join("baseline.json");
    let output_dir = temp.path().join("evidence");
    let ay_stub = temp.path().join("ay-unknown-stub");
    write_minimal_chc_comp_root(&benchmark_root, &["BV-Lin"], trivial_sat_chc());
    fs::write(
        &baseline_path,
        format!(
            "{}\n",
            serde_json::to_string_pretty(&json!({
                "suite": "test-chc-baseline",
                "benchmarks_dir": benchmark_root.display().to_string(),
                "timeout_sec": 2,
                "baseline_commit": "test-baseline",
                "baseline_date": "2026-05-04",
                "benchmarks_total": 1,
                "solved_total": 1,
                "benchmarks": [{
                    "file": "smoke/BV_Lin.smt2",
                    "status": "sat",
                    "elapsed_ms": 100,
                    "expected_status": "sat"
                }]
            }))
            .expect("serialize baseline")
        ),
    )
    .expect("write baseline");
    fs::write(
        &ay_stub,
        "#!/usr/bin/env bash\n\
         if [[ \"$*\" == *--version* ]]; then\n\
           printf 'ay unknown stub\\n'\n\
           printf 'build.stamp=unknown-stub\\n'\n\
           exit 0\n\
         fi\n\
         printf 'unknown\\n'\n",
    )
    .expect("write ay unknown stub");
    fs::set_permissions(&ay_stub, fs::Permissions::from_mode(0o755))
        .expect("chmod ay unknown stub");

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "preflight", "chc-baseline-compare"])
        .args(["--baseline"])
        .arg(&baseline_path)
        .args(["--bench-dir"])
        .arg(&benchmark_root)
        .args(["--ay"])
        .arg(&ay_stub)
        .args(["--output-dir"])
        .arg(&output_dir)
        .output()
        .expect("run failing CHC baseline compare through Rust CLI");
    assert!(
        !output.status.success(),
        "direct regression compare must fail; stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("status=fail evidence=chc-baseline-compare"));
    assert!(!stdout.contains("status=pass evidence=chc-baseline-compare"));

    let payload_text =
        fs::read_to_string(output_dir.join("chc-baseline-compare.json")).expect("evidence JSON");
    let payload: Value = serde_json::from_str(&payload_text).expect("evidence JSON parses");
    assert_eq!(payload["summary"]["direct_regressions"], 1);
}

#[test]
#[cfg(unix)]
fn submission_preflight_chc_comp_verify_rejects_manifest_archive_sha_mismatch() {
    let temp = tempdir().expect("temp dir");
    let package_dir = temp.path().join("chc-package");
    let json_path = temp.path().join("verify-archive-sha.json");
    let report_path = temp.path().join("verify-archive-sha.md");

    let package_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "package", "chc", "--output"])
        .arg(&package_dir)
        .args(["--ay-bin", env!("CARGO_BIN_EXE_ay")])
        .output()
        .expect("run ay submission package chc");
    assert_command_success(&package_output, "package chc");

    let staging_dir = temp.path().join("changed-chc-archive");
    let archive_root = copy_chc_archive_payload(&package_dir, &staging_dir);
    fs::write(
        archive_root.join("README.md"),
        "# changed archive payload without MANIFEST update\n",
    )
    .expect("change staged CHC README");
    rewrite_chc_archive(&package_dir, &staging_dir);

    let verify_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "preflight", "chc-comp-verify", "--package"])
        .arg(&package_dir)
        .args(["--skip-benchmark-smoke", "--json"])
        .arg(&json_path)
        .args(["--report"])
        .arg(&report_path)
        .output()
        .expect("run ay CHC-COMP verify");
    assert!(
        !verify_output.status.success(),
        "archive SHA mismatch must fail CHC-COMP verify; stdout={} stderr={}",
        String::from_utf8_lossy(&verify_output.stdout),
        String::from_utf8_lossy(&verify_output.stderr)
    );

    let payload_text = fs::read_to_string(&json_path).expect("verify JSON");
    let payload: Value = serde_json::from_str(&payload_text).expect("verify JSON parses");
    assert_eq!(payload["summary"]["actual_prove_ready"], false);
    assert!(payload["checks"]
        .as_array()
        .expect("checks")
        .iter()
        .any(|check| check["name"] == "manifest:archive_sha256" && check["status"] == "fail"));
    let report = fs::read_to_string(&report_path).expect("verify Markdown");
    assert!(report.contains("manifest:archive_sha256"));
}

#[test]
#[cfg(unix)]
fn submission_preflight_chc_comp_verify_smokes_archived_wrapper_not_package_tree() {
    let temp = tempdir().expect("temp dir");
    let package_dir = temp.path().join("chc-package");
    let benchmark_root = temp.path().join("chc-comp26-benchmarks");
    let json_path = temp.path().join("verify-archive-wrapper.json");
    let report_path = temp.path().join("verify-archive-wrapper.md");
    write_minimal_chc_comp_root(&benchmark_root, &CHC_TEST_ALL_TRACKS, trivial_sat_chc());

    let package_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "package", "chc", "--output"])
        .arg(&package_dir)
        .args(["--ay-bin", env!("CARGO_BIN_EXE_ay")])
        .output()
        .expect("run ay submission package chc");
    assert_command_success(&package_output, "package chc");

    let staging_dir = temp.path().join("unknown-wrapper-chc-archive");
    let archive_root = copy_chc_archive_payload(&package_dir, &staging_dir);
    fs::write(
        archive_root.join("run_solver.sh"),
        "#!/usr/bin/env bash\nprintf 'unknown\\n'\n",
    )
    .expect("write archive wrapper returning unknown");
    fs::set_permissions(
        archive_root.join("run_solver.sh"),
        fs::Permissions::from_mode(0o755),
    )
    .expect("chmod archive wrapper returning unknown");
    rewrite_chc_archive(&package_dir, &staging_dir);
    let archive_sha = test_sha256_file(package_dir.join("ay-chccomp-2026-linux-x86_64.tar.gz"));
    update_chc_manifest_archive_sha(&package_dir, &archive_sha);

    let verify_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "preflight", "chc-comp-verify", "--package"])
        .arg(&package_dir)
        .args(["--benchmarks-root"])
        .arg(&benchmark_root)
        .args(["--benchmark-timeout-ms", "60000", "--json"])
        .arg(&json_path)
        .args(["--report"])
        .arg(&report_path)
        .output()
        .expect("run ay CHC-COMP verify");
    assert!(
        !verify_output.status.success(),
        "archive wrapper returning unknown must fail CHC-COMP verify; stdout={} stderr={}",
        String::from_utf8_lossy(&verify_output.stdout),
        String::from_utf8_lossy(&verify_output.stderr)
    );

    let payload_text = fs::read_to_string(&json_path).expect("verify JSON");
    let payload: Value = serde_json::from_str(&payload_text).expect("verify JSON parses");
    assert!(payload["checks"]
        .as_array()
        .expect("checks")
        .iter()
        .any(|check| check["name"] == "manifest:archive_sha256" && check["status"] == "pass"));
    let smoke = &payload["benchmarks"]["smokes"].as_array().expect("smokes")[0];
    assert_eq!(smoke["expected_status"], "sat");
    assert_eq!(smoke["actual_status"], "unknown");
    assert_eq!(smoke["passed"], false);
    let report = fs::read_to_string(&report_path).expect("verify Markdown");
    assert!(report.contains("## Benchmark Smokes"));
}

#[test]
#[cfg(unix)]
fn submission_preflight_chc_comp_verify_missing_package_wrapper_writes_reports() {
    let temp = tempdir().expect("temp dir");
    let package_dir = temp.path().join("chc-package");
    let benchmark_root = temp.path().join("chc-comp26-benchmarks");
    let json_path = temp.path().join("verify-missing-package-wrapper.json");
    let report_path = temp.path().join("verify-missing-package-wrapper.md");
    write_minimal_chc_comp_root(&benchmark_root, &CHC_TEST_ALL_TRACKS, trivial_sat_chc());

    let package_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "package", "chc", "--output"])
        .arg(&package_dir)
        .args(["--ay-bin", env!("CARGO_BIN_EXE_ay")])
        .output()
        .expect("run ay submission package chc");
    assert_command_success(&package_output, "package chc");
    fs::remove_file(package_dir.join("tool-archive/ay/run_solver.sh"))
        .expect("remove package tree CHC wrapper");

    let verify_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "preflight", "chc-comp-verify", "--package"])
        .arg(&package_dir)
        .args(["--benchmarks-root"])
        .arg(&benchmark_root)
        .args(["--benchmark-timeout-ms", "60000", "--json"])
        .arg(&json_path)
        .args(["--report"])
        .arg(&report_path)
        .output()
        .expect("run ay CHC-COMP verify");
    assert!(
        !verify_output.status.success(),
        "missing package wrapper must fail CHC-COMP verify without suppressing reports; stdout={} stderr={}",
        String::from_utf8_lossy(&verify_output.stdout),
        String::from_utf8_lossy(&verify_output.stderr)
    );

    let payload_text = fs::read_to_string(&json_path).expect("verify JSON");
    let payload: Value = serde_json::from_str(&payload_text).expect("verify JSON parses");
    assert_eq!(payload["summary"]["actual_prove_ready"], false);
    assert!(payload["checks"]
        .as_array()
        .expect("checks")
        .iter()
        .any(|check| check["name"] == "package:run_solver" && check["status"] == "fail"));
    assert!(payload["benchmarks"]["smokes"]
        .as_array()
        .expect("smokes")
        .iter()
        .any(|smoke| smoke["passed"] == true));
    let report = fs::read_to_string(&report_path).expect("verify Markdown");
    assert!(report.contains("package:run_solver"));
}

#[test]
#[cfg(unix)]
fn submission_preflight_pb_comp_verify_missing_package_writes_reports() {
    let temp = tempdir().expect("temp dir");
    let json_path = temp.path().join("pb-verify-missing.json");
    let report_path = temp.path().join("pb-verify-missing.md");

    let verify_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "preflight", "pb-comp-verify", "--package"])
        .arg(temp.path().join("missing-pb-package"))
        .args(["--skip-archive-check", "--timeout-ms", "30000", "--json"])
        .arg(&json_path)
        .args(["--report"])
        .arg(&report_path)
        .output()
        .expect("run ay PB-COMP verify");
    assert!(
        !verify_output.status.success(),
        "missing package must fail PB-COMP verify while writing reports; stdout={} stderr={}",
        String::from_utf8_lossy(&verify_output.stdout),
        String::from_utf8_lossy(&verify_output.stderr)
    );

    let payload_text = fs::read_to_string(&json_path).expect("verify JSON");
    let payload: Value = serde_json::from_str(&payload_text).expect("verify JSON parses");
    assert_eq!(payload["schema_version"], "ay.pbcomp-verify/v1");
    assert_eq!(payload["summary"]["actual_submission_ready"], false);
    assert!(payload["checks"]
        .as_array()
        .expect("checks")
        .iter()
        .any(|check| check["name"] == "package:directory" && check["status"] == "fail"));
    assert!(payload["checks"]
        .as_array()
        .expect("checks")
        .iter()
        .any(|check| check["name"] == "checker:exit" && check["status"] == "fail"));
    let report = fs::read_to_string(&report_path).expect("verify Markdown");
    assert!(report.contains("# PB-COMP 2026 Verify"));
    assert!(report.contains("package:directory"));
}

#[test]
#[cfg(unix)]
fn submission_package_chc_rejects_invalid_tracks() {
    let temp = tempdir().expect("temp dir");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "package", "chc", "--output"])
        .arg(temp.path().join("bad-chc"))
        .args([
            "--ay-bin",
            env!("CARGO_BIN_EXE_ay"),
            "--tracks",
            "LIA-Lin-Arrays-BV",
        ])
        .output()
        .expect("run ay submission package chc with invalid tracks");

    assert!(
        !output.status.success(),
        "invalid CHC track should fail; stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("invalid CHC track 'LIA-Lin-Arrays-BV'"));
    assert!(stderr.contains("set-file names or public aliases"));
}

#[test]
#[cfg(unix)]
fn submission_package_chc_canonicalizes_public_nonlin_aliases_in_all_track_set() {
    let temp = tempdir().expect("temp dir");
    let out = temp.path().join("alias-chc");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "package", "chc", "--output"])
        .arg(&out)
        .args([
            "--ay-bin",
            env!("CARGO_BIN_EXE_ay"),
            "--tracks",
            "BOOL,BV-Nonlin,BV-Lin,LRA-Lin,LIA-Lin,LIA-Nonlin,LIA-Lin-Arrays,LIA-Nonlin-Arrays,ADT-LIA,ADT-LIA-Arrays,mixed_LIA_LRA",
        ])
        .output()
        .expect("run ay submission package chc with public nonlin aliases");

    assert_command_success(&output, "package chc with public nonlin aliases");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("track-model official_chc_comp_2026_tracks=9"));
    assert!(stdout.contains("track-aliases BV=BV-Nonlin LIA=LIA-Nonlin"));
    let chc_xml = fs::read_to_string(out.join("pr/benchmark-defs/ay.xml.template"))
        .expect("read alias CHC XML");
    for track in [
        "BOOL",
        "BV",
        "BV-Lin",
        "LRA-Lin",
        "LIA-Lin",
        "LIA",
        "LIA-Lin-Arrays",
        "LIA-Arrays",
        "ADT-LIA",
        "ADT-LIA-Arrays",
        "mixed_LIA_LRA",
    ] {
        assert!(chc_xml.contains(&format!(r#"<tasks name="{track}">"#)));
        assert!(chc_xml.contains(&format!(
            "<includesfile>../chc-comp26-benchmarks/{track}.set</includesfile>"
        )));
    }
    for alias in ["BV-Nonlin", "LIA-Nonlin", "LIA-Nonlin-Arrays"] {
        assert!(!chc_xml.contains(&format!(r#"<tasks name="{alias}">"#)));
    }
}

#[test]
#[cfg(unix)]
fn submission_package_chc_accepts_late_entry_artifact_replay_tracks() {
    let output = Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import importlib.util
import sys
from pathlib import Path

spec = importlib.util.spec_from_file_location(
    "artifact_check",
    Path("scripts/chccomp_late_entry_artifact_build_check.py"),
)
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
print(",".join(module.TRACKS))
"#,
        )
        .current_dir(workspace_root())
        .output()
        .expect("read CHC artifact replay tracks");
    assert_command_success(&output, "read CHC artifact replay tracks");

    let tracks = String::from_utf8(output.stdout).expect("tracks are utf8");
    let temp = tempdir().expect("temp dir");
    let package_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "package", "chc", "--output"])
        .arg(temp.path().join("replay-chc"))
        .args([
            "--ay-bin",
            env!("CARGO_BIN_EXE_ay"),
            "--tracks",
            tracks.trim(),
        ])
        .output()
        .expect("run ay submission package chc with artifact replay tracks");

    assert_command_success(&package_output, "package chc with artifact replay tracks");
}

#[test]
#[cfg(unix)]
fn submission_preflight_chc_late_entry_stub_writes_reports() {
    let temp = tempdir().expect("temp dir");
    let work_dir = temp.path().join("work");
    let json_path = temp.path().join("preflight.json");
    let report_path = temp.path().join("preflight.md");

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "preflight", "chc-late-entry", "--work-dir"])
        .arg(&work_dir)
        .args(["--json"])
        .arg(&json_path)
        .args(["--report"])
        .arg(&report_path)
        .output()
        .expect("run ay CHC late-entry preflight");
    assert_command_success(&output, "CHC late-entry preflight");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("status=pass actual_submission_ready=false local_only=true"));

    let payload_text = fs::read_to_string(&json_path).expect("preflight JSON");
    let payload: Value = serde_json::from_str(&payload_text).expect("preflight JSON parses");
    assert_eq!(
        payload["schema_version"],
        "ay.chccomp-late-entry-preflight/v1"
    );
    assert_eq!(payload["validation_mode"], "local-stub-archive");
    assert_eq!(payload["actual_submission_ready"], false);
    assert_eq!(payload["real_linux_artifact_available"], false);
    assert_eq!(payload["binary"]["platform"], "script-stub");
    assert_eq!(payload["track_model"]["official_track_count"], 9);
    assert_eq!(payload["track_model"]["local_set_file_category_count"], 11);
    assert_eq!(
        payload["local_set_file_categories"]
            .as_array()
            .expect("local set-file categories")
            .len(),
        CHC_TEST_ALL_TRACKS.len()
    );
    assert!(payload["archive"]["members"]
        .as_array()
        .expect("archive members")
        .iter()
        .any(|member| member == "ay/run_solver.sh"));
    assert!(payload["checks"]
        .as_array()
        .expect("checks")
        .iter()
        .any(
            |check| check["name"] == "wrapper_case:first-status-wins" && check["status"] == "pass"
        ));
    assert!(payload["wrapper_cases"]
        .as_array()
        .expect("wrapper cases")
        .iter()
        .any(|case| case["name"] == "crash-fallback"
            && case["expected"] == "unknown"
            && case["passed"] == true));

    let report = fs::read_to_string(&report_path).expect("preflight Markdown");
    assert!(report.contains("# CHC-COMP 2026 Late-Entry Local Preflight"));
    assert!(report.contains("## Track Model"));
    assert!(report.contains("## Wrapper Matrix"));
}

#[test]
#[cfg(unix)]
fn submission_preflight_chc_comp_verify_passes_minimal_benchmark_mirror() {
    // Serialize against the other real-solver benchmark-smoke test so the two do
    // not contend for CPU (and the solver's derived internal deadline) when the
    // full group_cli binary runs in parallel.
    let _serial = chc_solver_smoke_guard();
    let temp = tempdir().expect("temp dir");
    let package_dir = temp.path().join("chc-package");
    let benchmark_root = temp.path().join("chc-comp26-benchmarks");
    let json_path = temp.path().join("verify.json");
    let report_path = temp.path().join("verify.md");
    write_minimal_chc_comp_root(&benchmark_root, &CHC_TEST_ALL_TRACKS, trivial_sat_chc());

    let package_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "package", "chc", "--output"])
        .arg(&package_dir)
        .args([
            "--ay-bin",
            env!("CARGO_BIN_EXE_ay"),
            "--archive-url",
            "https://example.com/ay-chccomp-2026-linux-x86_64.tar.gz",
        ])
        .output()
        .expect("run ay submission package chc");
    assert_command_success(&package_output, "package chc");

    let verify_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "preflight", "chc-comp-verify", "--package"])
        .arg(&package_dir)
        .args(["--benchmarks-root"])
        .arg(&benchmark_root)
        .args([
            "--require-current-build",
            "--require-public-urls",
            "--benchmark-timeout-ms",
            "60000",
            "--json",
        ])
        .arg(&json_path)
        .args(["--report"])
        .arg(&report_path)
        .output()
        .expect("run ay CHC-COMP verify");
    assert_command_success(&verify_output, "CHC-COMP verify");
    let stdout = String::from_utf8_lossy(&verify_output.stdout);
    assert!(stdout.contains("status=pass actual_prove_ready=true"));
    assert!(stdout.contains("track-model official_chc_comp_2026_tracks=9"));
    assert!(stdout.contains("local_set_file_categories=11"));

    let payload_text = fs::read_to_string(&json_path).expect("verify JSON");
    let payload: Value = serde_json::from_str(&payload_text).expect("verify JSON parses");
    assert_eq!(payload["schema_version"], "ay.chccomp-verify/v1");
    assert_eq!(payload["summary"]["actual_prove_ready"], true);
    assert_eq!(payload["summary"]["fail_count"], 0);
    assert_eq!(
        payload["requirements"]["track_model"]["official_track_count"],
        9
    );
    assert_eq!(
        payload["requirements"]["track_model"]["local_set_file_category_count"],
        11
    );
    assert_eq!(
        payload["requirements"]["track_model"]["local_to_official_category_map"]
            .as_array()
            .expect("track model rows")
            .len(),
        CHC_TEST_ALL_TRACKS.len()
    );
    assert_eq!(
        payload["requirements"]["local_set_file_categories"]
            .as_array()
            .expect("local set-file categories")
            .len(),
        CHC_TEST_ALL_TRACKS.len()
    );
    assert_eq!(
        payload["benchmarks"]["smokes"]
            .as_array()
            .expect("benchmark smokes")
            .len(),
        CHC_TEST_ALL_TRACKS.len()
    );
    assert!(payload["benchmarks"]["smokes"]
        .as_array()
        .expect("benchmark smokes")
        .iter()
        .all(|smoke| smoke["solver_timeout_ms"] == 54000));
    assert!(payload["checks"]
        .as_array()
        .expect("checks")
        .iter()
        .any(|check| check["name"] == "xml:track_includes" && check["status"] == "pass"));

    let report = fs::read_to_string(&report_path).expect("verify Markdown");
    assert!(report.contains("# CHC-COMP 2026 Verify"));
    assert!(report.contains("## Track Model"));
    assert!(report.contains("Official CHC-COMP 2026 planned tracks: 9"));
    assert!(report.contains("Local chc-comp26 set-file categories used by this CLI: 11"));
    assert!(report.contains("Samples per local set-file category"));
    assert!(report.contains("| Local category | Input | Expected | Actual | Exit | Timeout |"));
    assert!(report.contains("## Benchmark Smokes"));
}

#[test]
#[cfg(unix)]
fn submission_prepare_chc_packages_gates_and_verifies_minimal_mirror() {
    // Same real-solver benchmark-smoke contention class as the verify/worker
    // mirror tests: it asserts a successful trivial-CHC solve, so serialize it
    // with them to avoid concurrent solver load under the full parallel run.
    let _serial = chc_solver_smoke_guard();
    let temp = tempdir().expect("temp dir");
    let package_dir = temp.path().join("chc-prepare-package");
    let benchmark_root = temp.path().join("chc-comp26-benchmarks");
    let json_path = temp.path().join("prepare-verify.json");
    let report_path = temp.path().join("prepare-verify.md");
    write_minimal_chc_comp_root(&benchmark_root, &CHC_TEST_ALL_TRACKS, trivial_sat_chc());

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "prepare", "chc", "--output"])
        .arg(&package_dir)
        .args([
            "--ay-bin",
            env!("CARGO_BIN_EXE_ay"),
            "--archive-url",
            "https://example.com/ay-chccomp-2026-linux-x86_64.tar.gz",
            "--benchmarks-root",
        ])
        .arg(&benchmark_root)
        .args(["--benchmark-timeout-ms", "60000", "--json"])
        .arg(&json_path)
        .args(["--report"])
        .arg(&report_path)
        .output()
        .expect("run ay submission prepare chc");
    assert_command_success(&output, "CHC-COMP prepare");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("status=pass prepared=true competition=chc-comp profile=local"));
    assert!(stdout.contains("track-model official_chc_comp_2026_tracks=9"));
    assert_file_exists(package_dir.join("ay-chccomp-2026-linux-x86_64.tar.gz"));

    let payload_text = fs::read_to_string(&json_path).expect("prepare verify JSON");
    let payload: Value = serde_json::from_str(&payload_text).expect("prepare verify JSON parses");
    assert_eq!(payload["schema_version"], "ay.chccomp-verify/v1");
    assert_eq!(payload["summary"]["actual_prove_ready"], true);
    assert_eq!(
        payload["benchmarks"]["smokes"]
            .as_array()
            .expect("benchmark smokes")
            .len(),
        CHC_TEST_ALL_TRACKS.len()
    );
    let report = fs::read_to_string(&report_path).expect("prepare verify Markdown");
    assert!(report.contains("# CHC-COMP 2026 Verify"));
    assert!(report.contains("## Track Model"));
}

#[test]
#[cfg(unix)]
fn submission_preflight_chc_comp_verify_rejects_stale_manifest_commit() {
    let temp = tempdir().expect("temp dir");
    let package_dir = temp.path().join("chc-package");
    let json_path = temp.path().join("verify-stale.json");
    let report_path = temp.path().join("verify-stale.md");

    let package_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "package", "chc", "--output"])
        .arg(&package_dir)
        .args(["--ay-bin", env!("CARGO_BIN_EXE_ay")])
        .output()
        .expect("run ay submission package chc");
    assert_command_success(&package_output, "package chc");

    let manifest_path = package_dir.join("MANIFEST.json");
    let mut manifest: Value = serde_json::from_str(
        &fs::read_to_string(&manifest_path).expect("read CHC package manifest"),
    )
    .expect("manifest JSON parses");
    manifest["generated_by"]["commit"] = Value::String("stale-commit".to_string());
    fs::write(
        &manifest_path,
        format!(
            "{}\n",
            serde_json::to_string_pretty(&manifest).expect("serialize stale manifest")
        ),
    )
    .expect("write stale manifest");

    let verify_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "preflight", "chc-comp-verify", "--package"])
        .arg(&package_dir)
        .args([
            "--skip-benchmark-smoke",
            "--require-current-build",
            "--json",
        ])
        .arg(&json_path)
        .args(["--report"])
        .arg(&report_path)
        .output()
        .expect("run ay CHC-COMP verify");
    assert!(
        !verify_output.status.success(),
        "stale manifest must fail CHC-COMP verify; stdout={} stderr={}",
        String::from_utf8_lossy(&verify_output.stdout),
        String::from_utf8_lossy(&verify_output.stderr)
    );
    let payload_text = fs::read_to_string(&json_path).expect("verify JSON");
    let payload: Value = serde_json::from_str(&payload_text).expect("verify JSON parses");
    assert_eq!(payload["summary"]["actual_prove_ready"], false);
    assert!(payload["checks"]
        .as_array()
        .expect("checks")
        .iter()
        .any(|check| check["name"] == "manifest:current_build" && check["status"] == "fail"));
}

#[test]
#[cfg(unix)]
fn submission_preflight_chc_comp_verify_rejects_expected_sat_unsolved_smoke() {
    let temp = tempdir().expect("temp dir");
    let package_dir = temp.path().join("chc-package");
    let benchmark_root = temp.path().join("chc-comp26-benchmarks");
    let json_path = temp.path().join("verify-unknown.json");
    let report_path = temp.path().join("verify-unknown.md");
    write_minimal_chc_comp_root(&benchmark_root, &CHC_TEST_ALL_TRACKS, trivial_sat_chc());
    fs::remove_file(benchmark_root.join("smoke/BV_Lin.smt2"))
        .expect("remove smoke input to force wrapper unknown fallback");

    let package_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "package", "chc", "--output"])
        .arg(&package_dir)
        .args(["--ay-bin", env!("CARGO_BIN_EXE_ay")])
        .output()
        .expect("run ay submission package chc");
    assert_command_success(&package_output, "package chc");

    let verify_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "preflight", "chc-comp-verify", "--package"])
        .arg(&package_dir)
        .args(["--benchmarks-root"])
        .arg(&benchmark_root)
        .args(["--benchmark-timeout-ms", "60000", "--json"])
        .arg(&json_path)
        .args(["--report"])
        .arg(&report_path)
        .output()
        .expect("run ay CHC-COMP verify");
    assert!(
        !verify_output.status.success(),
        "expected sat benchmark returning unknown must fail CHC-COMP verify; stdout={} stderr={}",
        String::from_utf8_lossy(&verify_output.stdout),
        String::from_utf8_lossy(&verify_output.stderr)
    );
    let payload_text = fs::read_to_string(&json_path).expect("verify JSON");
    let payload: Value = serde_json::from_str(&payload_text).expect("verify JSON parses");
    let smoke = payload["benchmarks"]["smokes"]
        .as_array()
        .expect("smokes")
        .iter()
        .find(|smoke| smoke["input"] == "BV_Lin.smt2")
        .expect("BV-Lin smoke");
    assert_eq!(smoke["expected_status"], "sat");
    assert_ne!(smoke["actual_status"], "sat");
    assert_eq!(smoke["passed"], false);
}

#[test]
fn submission_preflight_chc_comp_verify_removed_aliases_do_not_parse() {
    for alias in ["chc-audit", "chc-prove-ready"] {
        let output = Command::new(env!("CARGO_BIN_EXE_ay"))
            .args(["submission", "preflight", alias, "--help"])
            .output()
            .expect("run removed CHC-COMP verify alias");
        assert!(
            !output.status.success(),
            "removed alias {alias} must not parse; stdout={} stderr={}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("unrecognized subcommand") && stderr.contains(alias),
            "removed alias {alias} should be rejected as an unknown subcommand; stderr={stderr}"
        );
    }
}

#[test]
fn submission_worker_chc_comp_help_lists_factory_commands() {
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "worker", "chc-comp", "--help"])
        .output()
        .expect("run CHC worker help");
    assert_command_success(&output, "CHC worker help");
    let stdout = String::from_utf8_lossy(&output.stdout);
    for command in ["bootstrap", "shard-plan", "run", "audit"] {
        assert!(
            stdout.contains(command),
            "worker help should list {command}; stdout={stdout}"
        );
    }
}

#[test]
#[cfg(unix)]
fn submission_worker_chc_comp_run_writes_report_and_audit_accepts() {
    // Serialize against the other real-solver benchmark-smoke test so the two do
    // not contend for CPU (and the solver's derived internal deadline) when the
    // full group_cli binary runs in parallel.
    let _serial = chc_solver_smoke_guard();
    let temp = tempdir().expect("temp dir");
    let package_dir = temp.path().join("chc-package");
    let benchmark_root = temp.path().join("chc-comp26-benchmarks");
    let worker_json = temp.path().join("worker-run.json");
    let worker_report = temp.path().join("worker-run.md");
    let audit_json = temp.path().join("worker-audit.json");
    let audit_report = temp.path().join("worker-audit.md");
    write_minimal_chc_comp_root(&benchmark_root, &["BV-Lin"], trivial_sat_chc());

    let package_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "package", "chc", "--output"])
        .arg(&package_dir)
        .args(["--ay-bin", env!("CARGO_BIN_EXE_ay")])
        .output()
        .expect("run ay submission package chc");
    assert_command_success(&package_output, "package chc");

    let worker_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args([
            "submission",
            "worker",
            "chc-comp",
            "run",
            "--issue",
            "9692",
            "--lane",
            "test-lane",
            "--tracks",
            "BV-Lin",
            "--samples-per-track",
            "1",
            "--benchmark-timeout-ms",
            "60000",
            "--allow-dirty",
            "--no-gh",
            "--package",
        ])
        .arg(&package_dir)
        .args(["--benchmarks-root"])
        .arg(&benchmark_root)
        .args(["--json"])
        .arg(&worker_json)
        .args(["--report"])
        .arg(&worker_report)
        .output()
        .expect("run CHC worker lane");
    assert_command_success(&worker_output, "CHC worker lane");

    let payload_text = fs::read_to_string(&worker_json).expect("worker JSON");
    let payload: Value = serde_json::from_str(&payload_text).expect("worker JSON parses");
    assert_eq!(payload["schema_version"], "ay.chccomp-worker-report/v1");
    assert_eq!(payload["kind"], "run");
    assert_eq!(payload["issue"], 9692);
    assert_eq!(payload["summary"]["total_cases"], 1);
    assert_eq!(payload["summary"]["failed_cases"], 0);
    assert_eq!(payload["summary"]["solved"], 1);
    assert_eq!(payload["track_model"]["official_track_count"], 9);
    assert_eq!(payload["track_model"]["local_set_file_category_count"], 11);
    assert_eq!(
        payload["track_model"]["legacy_tracks_field_note"].as_str(),
        Some("Legacy JSON field `tracks` is retained for compatibility and means local set-file categories; new consumers should read `local_set_file_categories` or `track_model`.")
    );
    assert_eq!(payload["tracks"][0], "BV-Lin");
    assert!(worker_report.is_file());
    let worker_markdown = fs::read_to_string(&worker_report).expect("worker Markdown");
    assert!(worker_markdown.contains("## Track Model"));
    assert!(worker_markdown.contains("Official CHC-COMP 2026 planned tracks: 9"));
    assert!(worker_markdown.contains("Local chc-comp26 set-file categories used by this CLI: 11"));
    assert!(worker_markdown.contains("| Local category | Input | Expected | Actual | Timeout |"));

    let audit_output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "worker", "chc-comp", "audit"])
        .arg(&worker_json)
        .args(["--allow-dirty", "--allow-stale-package", "--json"])
        .arg(&audit_json)
        .args(["--report"])
        .arg(&audit_report)
        .output()
        .expect("audit CHC worker report");
    assert_command_success(&audit_output, "CHC worker audit");
    let audit_payload: Value =
        serde_json::from_str(&fs::read_to_string(&audit_json).expect("worker audit JSON"))
            .expect("worker audit JSON parses");
    assert_eq!(audit_payload["summary"]["audit_ready"], true);
    assert!(audit_report.is_file());
}

#[test]
// cfg(unix): uses `fs`, whose import this file gates on unix (the sibling
// packaging tests are unix-only); without the gate the whole group_cli
// target fails to COMPILE on Windows (found 2026-07-14 by the
// experimental-feature compile lane).
#[cfg(unix)]
fn submission_worker_chc_comp_audit_rejects_dirty_report_by_default() {
    let temp = tempdir().expect("temp dir");
    let report_json = temp.path().join("dirty-worker.json");
    let audit_json = temp.path().join("dirty-audit.json");
    let synthetic = json!({
        "schema_version": "ay.chccomp-worker-report/v1",
        "kind": "run",
        "issue": 9692,
        "lane": "dirty",
        "repo": {
            "commit": "abc123",
            "dirty": true
        },
        "package_manifest_commit": "abc123",
        "binary_sha256": "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        "summary": {
            "total_cases": 1,
            "solved": 1,
            "wrong": 0,
            "invalid": 0,
            "stdout_clean_failures": 0,
            "failed_cases": 0
        },
        "cases": [{
            "track": "BV-Lin",
            "path": "case.smt2",
            "expected": "sat",
            "actual": "sat",
            "timed_out": false,
            "stdout_status_clean": true,
            "passed": true
        }]
    });
    fs::write(
        &report_json,
        format!(
            "{}\n",
            serde_json::to_string_pretty(&synthetic).expect("serialize synthetic report")
        ),
    )
    .expect("write synthetic worker report");

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["submission", "worker", "chc-comp", "audit"])
        .arg(&report_json)
        .args(["--json"])
        .arg(&audit_json)
        .output()
        .expect("audit dirty synthetic report");
    assert!(
        !output.status.success(),
        "dirty worker report should fail audit; stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let audit_payload: Value =
        serde_json::from_str(&fs::read_to_string(&audit_json).expect("dirty audit JSON"))
            .expect("dirty audit JSON parses");
    assert_eq!(audit_payload["summary"]["audit_ready"], false);
    assert!(audit_payload["checks"]
        .as_array()
        .expect("audit checks")
        .iter()
        .any(
            |check| check["name"].as_str().unwrap_or("").contains(":dirty")
                && check["status"] == "fail"
        ));
}

#[test]
#[cfg(unix)]
fn direct_chc_frontend_parse_failure_emits_competition_status() {
    let temp = tempdir().expect("temp dir");
    let input = temp.path().join("bad-chc.smt2");
    fs::write(&input, "(set-logic HORN)\n(assert\n(check-sat)\n").expect("write bad CHC input");

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--chc")
        .arg(&input)
        .output()
        .expect("run ay --chc on bad input");
    assert!(
        output.status.success(),
        "direct --chc frontend failures should degrade to a status-clean unknown; stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.lines().any(|line| line.trim() == "unknown"),
        "direct --chc frontend failure must print a bare unknown status; stdout={stdout}"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("parse error") && stderr.contains("reason-unknown"),
        "direct --chc frontend failure should explain the unknown; stderr={stderr}"
    );
}

#[test]
#[cfg(unix)]
fn submission_preflight_python_wrapper_delegates_to_rust_cli() {
    let temp = tempdir().expect("temp dir");
    let json_path = temp.path().join("wrapper-preflight.json");
    let report_path = temp.path().join("wrapper-preflight.md");
    let output = Command::new("python3")
        .arg(workspace_root().join("scripts/chccomp_late_entry_preflight.py"))
        .args(["--work-dir"])
        .arg(temp.path().join("wrapper-work"))
        .args(["--json"])
        .arg(&json_path)
        .args(["--report"])
        .arg(&report_path)
        .env("AY_CLI", env!("CARGO_BIN_EXE_ay"))
        .output()
        .expect("run CHC preflight compatibility wrapper");
    assert_command_success(&output, "Python CHC preflight wrapper");
    let payload_text = fs::read_to_string(&json_path).expect("wrapper preflight JSON");
    let payload: Value =
        serde_json::from_str(&payload_text).expect("wrapper preflight JSON parses");
    assert_eq!(payload["validation_mode"], "local-stub-archive");
    assert!(report_path.is_file());
}

/// The generated SMT wrappers must RUN, not merely exist.
///
/// `run_solver_incr.sh` used to forward the benchmark as `"$@"` alongside `-in`.
/// `-in` maps to `--incremental`, which reads the command stream from stdin, and
/// ay deliberately rejects FILE + `--incremental` (main.rs:4956) rather than
/// silently ignoring the FILE. So the wrapper exited 1 on every benchmark — a
/// zero score for the entire Incremental track — while the package tests, which
/// only asserted the file existed, stayed green.
///
/// This executes each wrapper the way the competition does (benchmark as an
/// ARGUMENT) and asserts real verdicts come back.
#[test]
#[cfg(unix)]
fn generated_smt_wrappers_actually_solve_a_benchmark() {
    let temp = tempdir().expect("temp dir");
    let dir = temp.path();
    let ay_bin = env!("CARGO_BIN_EXE_ay");
    fs::copy(ay_bin, dir.join("ay")).expect("stage ay binary");
    fs::set_permissions(dir.join("ay"), fs::Permissions::from_mode(0o755)).expect("chmod ay");

    let out_dir = temp.path().join("gen");
    let output = Command::new(ay_bin)
        .args(["submission", "generate", "smt", "--output"])
        .arg(&out_dir)
        .output()
        .expect("run ay submission generator");
    assert_command_success(&output, "generator");

    // Three check-sats across a push/pop so an incremental wrapper that only
    // answers the first one is distinguishable from a correct one.
    let bench = dir.join("bench.smt2");
    fs::write(
        &bench,
        "(set-logic QF_LRA)\n(declare-fun x () Real)\n(assert (> x 1))\n(check-sat)\n\
         (push 1)\n(assert (< x 0))\n(check-sat)\n(pop 1)\n(check-sat)\n",
    )
    .expect("write benchmark");

    for (wrapper, expected) in [
        ("run_solver.sh", vec!["sat", "unsat", "sat"]),
        ("run_solver_incr.sh", vec!["sat", "unsat", "sat"]),
    ] {
        let src = out_dir.join(wrapper);
        let staged = dir.join(wrapper);
        fs::copy(&src, &staged).unwrap_or_else(|e| panic!("stage {wrapper}: {e}"));
        fs::set_permissions(&staged, fs::Permissions::from_mode(0o755)).expect("chmod wrapper");

        let run = Command::new(&staged)
            .arg(&bench)
            .env("STAREXEC_WALLCLOCK_LIMIT", "1200")
            .output()
            .unwrap_or_else(|e| panic!("run {wrapper}: {e}"));

        let stdout = String::from_utf8_lossy(&run.stdout);
        let stderr = String::from_utf8_lossy(&run.stderr);
        assert!(
            run.status.success(),
            "{wrapper} must exit 0 when given the benchmark as an argument \
             (this is exactly how the competition invokes it); stderr: {stderr}"
        );
        let verdicts: Vec<&str> = stdout
            .lines()
            .map(str::trim)
            .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
            .collect();
        assert_eq!(
            verdicts, expected,
            "{wrapper} verdicts; stdout: {stdout}; stderr: {stderr}"
        );
    }
}

/// The Model Validation wrapper must produce a MODEL, not just `sat`.
///
/// MV scores a `sat` answer only if the accompanying model validates, so an
/// invocation that answers correctly but emits no `define-fun` scores zero just
/// as surely as one that fails to start. `run_solver_mv.sh` is currently
/// byte-identical to `run_solver.sh`; this pins that it actually behaves like an
/// MV solver rather than merely existing.
#[test]
#[cfg(unix)]
fn generated_mv_wrapper_emits_a_model() {
    let temp = tempdir().expect("temp dir");
    let dir = temp.path();
    let ay_bin = env!("CARGO_BIN_EXE_ay");
    fs::copy(ay_bin, dir.join("ay")).expect("stage ay binary");
    fs::set_permissions(dir.join("ay"), fs::Permissions::from_mode(0o755)).expect("chmod ay");

    let out_dir = temp.path().join("gen");
    let output = Command::new(ay_bin)
        .args(["submission", "generate", "smt", "--output"])
        .arg(&out_dir)
        .output()
        .expect("run ay submission generator");
    assert_command_success(&output, "generator");

    let bench = dir.join("mv.smt2");
    fs::write(
        &bench,
        "(set-option :produce-models true)\n(set-logic QF_LRA)\n\
         (declare-fun x () Real)\n(assert (> x 1))\n(check-sat)\n(get-model)\n",
    )
    .expect("write benchmark");

    let staged = dir.join("run_solver_mv.sh");
    fs::copy(out_dir.join("run_solver_mv.sh"), &staged).expect("stage mv wrapper");
    fs::set_permissions(&staged, fs::Permissions::from_mode(0o755)).expect("chmod wrapper");

    let run = Command::new(&staged)
        .arg(&bench)
        .env("STAREXEC_WALLCLOCK_LIMIT", "1200")
        .output()
        .expect("run run_solver_mv.sh");

    let stdout = String::from_utf8_lossy(&run.stdout);
    let stderr = String::from_utf8_lossy(&run.stderr);
    assert!(
        run.status.success(),
        "run_solver_mv.sh must exit 0 with the benchmark as an argument; stderr: {stderr}"
    );
    assert!(
        stdout.lines().any(|l| l.trim() == "sat"),
        "run_solver_mv.sh must answer sat; stdout: {stdout}"
    );
    assert!(
        stdout.contains("define-fun"),
        "run_solver_mv.sh must emit a model for the sat answer, else MV scores it zero; \
         stdout: {stdout}"
    );
}

/// The Unsat Core track runs through `run_solver.sh` — there is no separate UC
/// wrapper — so the claimed UC division wins depend on that wrapper emitting a
/// core, and a MINIMAL one: UC scores `asserts - core_size`, so a solver that
/// returns every named assertion scores nothing on an instance it solved
/// correctly. Pinned here through the generated wrapper rather than the library.
#[test]
#[cfg(unix)]
fn generated_wrapper_emits_a_minimal_unsat_core() {
    let temp = tempdir().expect("temp dir");
    let dir = temp.path();
    let ay_bin = env!("CARGO_BIN_EXE_ay");
    fs::copy(ay_bin, dir.join("ay")).expect("stage ay binary");
    fs::set_permissions(dir.join("ay"), fs::Permissions::from_mode(0o755)).expect("chmod ay");

    let out_dir = temp.path().join("gen");
    let output = Command::new(ay_bin)
        .args(["submission", "generate", "smt", "--output"])
        .arg(&out_dir)
        .output()
        .expect("run ay submission generator");
    assert_command_success(&output, "generator");

    // a2 /\ a3 is already unsat (x < 0 and x > 5), so a1 must NOT appear.
    let bench = dir.join("uc.smt2");
    fs::write(
        &bench,
        "(set-option :produce-unsat-cores true)\n(set-logic QF_LRA)\n\
         (declare-fun x () Real)\n(assert (! (> x 1) :named a1))\n\
         (assert (! (< x 0) :named a2))\n(assert (! (> x 5) :named a3))\n\
         (check-sat)\n(get-unsat-core)\n",
    )
    .expect("write benchmark");

    let staged = dir.join("run_solver.sh");
    fs::copy(out_dir.join("run_solver.sh"), &staged).expect("stage wrapper");
    fs::set_permissions(&staged, fs::Permissions::from_mode(0o755)).expect("chmod wrapper");

    let run = Command::new(&staged)
        .arg(&bench)
        .env("STAREXEC_WALLCLOCK_LIMIT", "1200")
        .output()
        .expect("run run_solver.sh");

    let stdout = String::from_utf8_lossy(&run.stdout);
    let stderr = String::from_utf8_lossy(&run.stderr);
    assert!(
        run.status.success(),
        "run_solver.sh must exit 0 on a UC benchmark; stderr: {stderr}"
    );
    assert!(
        stdout.lines().any(|l| l.trim() == "unsat"),
        "UC path must answer unsat; stdout: {stdout}"
    );
    let core = stdout
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with('('))
        .unwrap_or_else(|| panic!("no core emitted; stdout: {stdout}"));
    assert!(
        core.contains("a2") && core.contains("a3"),
        "core must contain the contradictory pair; got {core}"
    );
    assert!(
        !core.contains("a1"),
        "core must be minimal — a1 is not needed for the contradiction, and UC scores \
         asserts-minus-core-size, so padding scores zero; got {core}"
    );
}
