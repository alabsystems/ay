// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    cell::Cell,
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    sync::{Arc, Mutex},
};

use ay_pb::{
    parse_opb,
    proof::{
        certify_opt_lin_bounds, certify_opt_lin_bounds_compact, certify_opt_lin_bounds_pb,
        ProofError,
    },
    PbCdclResult, PbCdclSolver, PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm,
};

#[derive(Clone)]
struct SharedBytes(Arc<Mutex<Vec<u8>>>);

impl SharedBytes {
    fn new() -> Self {
        Self(Arc::new(Mutex::new(Vec::new())))
    }

    fn as_string(&self) -> String {
        String::from_utf8(
            self.0
                .lock()
                .expect("proof writer mutex must not be poisoned")
                .clone(),
        )
        .expect("proof output must be valid UTF-8")
    }
}

impl std::io::Write for SharedBytes {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0
            .lock()
            .expect("proof writer mutex must not be poisoned")
            .extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn load_instance_source(name: &str) -> String {
    let path = format!("{}/tests/instances/{name}", env!("CARGO_MANIFEST_DIR"));
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("failed to read {path}: {e}"))
}

fn load_instance(name: &str) -> PbInstance {
    let content = load_instance_source(name);
    parse_opb(&content).unwrap_or_else(|e| panic!("failed to parse {name}: {e}"))
}

fn lit(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}

fn term(coeff: i128, lit: PbLit) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![lit],
    }
}

fn ge_constraint(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    }
}

fn exactly_one_instance(num_vars: u32) -> PbInstance {
    let objective = PbObjective {
        terms: (1..=num_vars).map(|var| term(1, lit(var))).collect(),
    };

    PbInstance {
        num_vars,
        num_constraints: 2,
        constraints: vec![
            ge_constraint((1..=num_vars).map(|var| term(1, lit(var))).collect(), 1),
            ge_constraint((1..=num_vars).map(|var| term(-1, lit(var))).collect(), -1),
        ],
        objective: Some(objective),
    }
}

fn verify_with_local_veripb(test_name: &str, opb: &str, proof: &str) {
    let Some(veripb) = find_local_veripb() else {
        eprintln!("skipping external VeriPB check for {test_name}: no local veripb found");
        return;
    };

    let stem = format!("ay-pb-{test_name}-{}", std::process::id());
    let formula_path = env::temp_dir().join(format!("{stem}.opb"));
    let proof_path = env::temp_dir().join(format!("{stem}.pbp"));

    fs::write(&formula_path, opb).expect("write temporary OPB formula for VeriPB");
    fs::write(&proof_path, proof).expect("write temporary VeriPB proof");

    let output = Command::new(veripb)
        .arg("--opb")
        .arg(&formula_path)
        .arg(&proof_path)
        .output()
        .expect("run local VeriPB checker");

    let _ = fs::remove_file(&formula_path);
    let _ = fs::remove_file(&proof_path);

    assert!(
        output.status.success(),
        "{test_name}: VeriPB rejected proof\nstatus: {:?}\nstdout: {}\nstderr: {}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Matches a proof's `conclusion BOUNDS` line against expected bare bounds,
/// accepting BOTH the bare and the hinted conclusion forms:
///   `conclusion BOUNDS <lb> <ub>;`
///   `conclusion BOUNDS <lb> : <id> <ub> : <witness literals...>;`
/// The hints (contradiction-row id, inline incumbent witness) are what make
/// the conclusion verifiable in unchecked-deletion mode; the BOUNDS values
/// themselves must still match exactly.
fn bounds_conclusion_matches(line: &str, expected_lower: &str, expected_upper: &str) -> bool {
    let Some(rest) = line.strip_prefix("conclusion BOUNDS ") else {
        return false;
    };
    let Some(rest) = rest.strip_suffix(';') else {
        return false;
    };
    let mut tokens = rest.split_whitespace().peekable();
    if tokens.next() != Some(expected_lower) {
        return false;
    }
    if tokens.peek() == Some(&":") {
        tokens.next();
        if tokens.next().is_none() {
            return false;
        }
    }
    if tokens.next() != Some(expected_upper) {
        return false;
    }
    match tokens.next() {
        None => true,
        Some(":") => tokens.next().is_some(),
        Some(_) => false,
    }
}

fn assert_opt_bounds_proof_contract(
    test_name: &str,
    opb: &str,
    proof: &str,
    expected_bounds: &str,
) {
    assert!(
        proof.lines().any(|line| line == "output NONE;"),
        "{test_name}: OPT proof must include the VeriPB output marker: {proof}"
    );
    let bounds = expected_bounds
        .strip_prefix("conclusion BOUNDS ")
        .and_then(|rest| rest.strip_suffix(';'))
        .unwrap_or_else(|| panic!("{test_name}: malformed expected bounds `{expected_bounds}`"));
    let mut bounds_tokens = bounds.split_whitespace();
    let (Some(expected_lower), Some(expected_upper), None) = (
        bounds_tokens.next(),
        bounds_tokens.next(),
        bounds_tokens.next(),
    ) else {
        panic!("{test_name}: malformed expected bounds `{expected_bounds}`");
    };
    assert!(
        proof
            .lines()
            .any(|line| bounds_conclusion_matches(line, expected_lower, expected_upper)),
        "{test_name}: OPT proof must conclude exact bounds `{expected_bounds}` (bare or hinted): {proof}"
    );
    assert!(
        !proof
            .lines()
            .any(|line| line.starts_with("conclusion SAT") || line.starts_with("conclusion UNSAT")),
        "{test_name}: OPT proof must not terminate as a decision proof: {proof}"
    );
    assert!(
        proof.lines().last() == Some("end pseudo-Boolean proof;"),
        "{test_name}: OPT proof must end with the VeriPB proof terminator: {proof}"
    );

    verify_with_local_veripb(test_name, opb, proof);
}

fn assert_feasible_opt_proof_contract(
    test_name: &str,
    opb: &str,
    proof: &str,
    expected_bounds: &str,
    expected_soli: Option<&str>,
) {
    match expected_soli {
        Some(line) => assert!(
            proof.lines().any(|proof_line| proof_line == line),
            "{test_name}: OPT proof must log expected VeriPB solution-improving row `{line}`: {proof}"
        ),
        None => assert!(
            proof.lines().any(|line| line.starts_with("soli ")),
            "{test_name}: OPT proof must log at least one VeriPB solution-improving row: {proof}"
        ),
    }

    assert_opt_bounds_proof_contract(test_name, opb, proof, expected_bounds);
}

/// Re-checks a proof in UNCHECKED-DELETION mode (`veripb -u`), where the
/// checker discounts `soli`-logged solutions: a finite-bound `conclusion
/// BOUNDS` only verifies there when it carries BOTH hints (contradiction-row
/// id + inline incumbent witness). New cert routes keep regressing exactly
/// this, so the PB-native tests pin both deletion modes. Skips (like
/// [`verify_with_local_veripb`]) when no local checker is found.
fn verify_with_local_veripb_unchecked_deletions(test_name: &str, opb: &str, proof: &str) {
    let Some(veripb) = find_local_veripb() else {
        eprintln!("skipping external VeriPB -u check for {test_name}: no local veripb found");
        return;
    };

    let stem = format!("ay-pb-{test_name}-u-{}", std::process::id());
    let formula_path = env::temp_dir().join(format!("{stem}.opb"));
    let proof_path = env::temp_dir().join(format!("{stem}.pbp"));

    fs::write(&formula_path, opb).expect("write temporary OPB formula for VeriPB -u");
    fs::write(&proof_path, proof).expect("write temporary VeriPB proof for -u");

    let output = Command::new(veripb)
        .arg("-u")
        .arg("--opb")
        .arg(&formula_path)
        .arg(&proof_path)
        .output()
        .expect("run local VeriPB checker in unchecked-deletion mode");

    let _ = fs::remove_file(&formula_path);
    let _ = fs::remove_file(&proof_path);

    assert!(
        output.status.success(),
        "{test_name}: VeriPB -u (unchecked deletions) rejected proof\nstatus: {:?}\nstdout: {}\nstderr: {}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn find_local_veripb() -> Option<PathBuf> {
    for var in ["AY_PB26_VERIPB_BIN", "VERIPB_BIN", "VERIPB"] {
        if let Some(candidate) = env::var_os(var).map(PathBuf::from) {
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }

    for candidate in [Path::new("/tmp/veripb-3/bin/veripb")] {
        if candidate.is_file() {
            return Some(candidate.to_path_buf());
        }
    }

    env::var_os("PATH")
        .into_iter()
        .flat_map(|paths| env::split_paths(&paths).collect::<Vec<_>>())
        .map(|dir| dir.join("veripb"))
        .find(|candidate| candidate.is_file())
}

fn unique_temp_path(stem: &str, extension: &str) -> PathBuf {
    env::temp_dir().join(format!(
        "ay-pb-{stem}-{}-{}.{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|duration| duration.as_nanos())
            .unwrap_or(0),
        extension
    ))
}

fn run_standalone_ay_pb(
    args: &[&str],
    input_path: &Path,
) -> (std::process::ExitStatus, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_ay-pb"))
        .args(["pb", "solve"])
        .args(args)
        .arg(input_path)
        .output()
        .expect("standalone ay-pb binary should run");

    (
        output.status,
        String::from_utf8(output.stdout).expect("stdout should be utf-8"),
        String::from_utf8(output.stderr).expect("stderr should be utf-8"),
    )
}

fn write_temp_opb(stem: &str, content: &str) -> PathBuf {
    let path = unique_temp_path(stem, "opb");
    fs::write(&path, content).expect("write temporary OPB input");
    path
}

#[test]
fn test_unsat_proof_logging_still_concludes_cleanly() {
    let instance = load_instance("unsat_simple.opb");
    let buf = SharedBytes::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");

    let result = solver.solve();
    assert_eq!(result, PbCdclResult::Unsatisfiable);
    solver
        .conclude_proof()
        .expect("UNSAT proof logging must still conclude successfully");

    let proof = buf.as_string();
    assert!(
        proof.lines().any(|line| line == "output NONE;"),
        "UNSAT proof must declare an empty VeriPB output section: {proof}"
    );
    assert!(
        proof.lines().any(|line| line == "rup >= 1 ;"),
        "UNSAT proof must derive contradiction as an empty-left-hand-side RUP step: {proof}"
    );
    assert!(
        proof
            .lines()
            .any(|line| line.starts_with("conclusion UNSAT : ")),
        "UNSAT proof must conclude with a VeriPB UNSAT footer: {proof}"
    );
    assert!(
        !proof.lines().any(|line| line.starts_with("c ")),
        "VeriPB v3 UNSAT proofs must not depend on the legacy checker-local c marker: {proof}"
    );
    assert!(
        proof.lines().last() == Some("end pseudo-Boolean proof;"),
        "UNSAT proof must end with the VeriPB proof terminator: {proof}"
    );
}

#[test]
fn test_standalone_cli_le_opb_unsat_proof_verifies_original_source() {
    let opb = "* #variable= 1 #constraint= 2\n+1 x1 <= 0 ;\n+1 x1 >= 1 ;\n";
    let input_path = write_temp_opb("cli-le-unsat", opb);
    let proof_path = unique_temp_path("cli-le-unsat", "pbp");
    let proof_arg = proof_path
        .to_str()
        .expect("temporary proof path should be utf-8");

    let (status, stdout, stderr) =
        run_standalone_ay_pb(&["--timeout", "5000", "--proof", proof_arg], &input_path);

    assert_eq!(
        status.code(),
        Some(20),
        "standalone <= UNSAT proof request should exit UNSAT; stdout: {stdout}; stderr: {stderr}"
    );
    assert!(
        stdout.contains("s UNSATISFIABLE\n"),
        "standalone <= UNSAT proof request should report UNSATISFIABLE: {stdout}"
    );
    let proof = fs::read_to_string(&proof_path).expect("proof file should be readable");
    assert!(
        proof
            .lines()
            .any(|line| line.starts_with("conclusion UNSAT : ")),
        "standalone <= UNSAT proof should conclude UNSAT: {proof}"
    );
    verify_with_local_veripb("standalone_cli_le_unsat", opb, &proof);

    let _ = fs::remove_file(&input_path);
    let _ = fs::remove_file(&proof_path);
}

#[test]
fn test_standalone_cli_le_opb_opt_proof_verifies_original_source_without_native_flag() {
    let opb = concat!(
        "* #variable= 2 #constraint= 2\n",
        "min: +1 x1 +2 x2 ;\n",
        "+1 x1 +1 x2 <= 1 ;\n",
        "+1 x1 +1 x2 >= 1 ;\n",
    );
    let input_path = write_temp_opb("cli-le-opt", opb);
    let proof_path = unique_temp_path("cli-le-opt", "pbp");
    let proof_arg = proof_path
        .to_str()
        .expect("temporary proof path should be utf-8");

    let (status, stdout, stderr) =
        run_standalone_ay_pb(&["--timeout", "5000", "--proof", proof_arg], &input_path);

    assert_eq!(
        status.code(),
        Some(30),
        "standalone <= OPT proof request should exit OPTIMUM FOUND; stdout: {stdout}; stderr: {stderr}"
    );
    assert!(
        stdout.lines().any(|line| line == "o 1"),
        "standalone <= OPT proof request should emit objective 1: {stdout}"
    );
    assert!(
        stdout.contains("s OPTIMUM FOUND\n"),
        "standalone <= OPT proof request should report OPTIMUM FOUND: {stdout}"
    );
    let proof = fs::read_to_string(&proof_path).expect("proof file should be readable");
    assert_feasible_opt_proof_contract(
        "standalone_cli_le_opt",
        opb,
        &proof,
        "conclusion BOUNDS 1 1;",
        None,
    );

    let _ = fs::remove_file(&input_path);
    let _ = fs::remove_file(&proof_path);
}

#[test]
fn test_standalone_cli_native_golomb_opb_opt_proof_verifies_original_source() {
    let opb = concat!(
        "* #variable= 4 #constraint= 6\n",
        "* order-3 Golomb shape: x1/x2 choose length 2/3; x3/x4 choose middle mark 1/2\n",
        "min: +2 x1 +3 x2 ;\n",
        "+1 x1 +1 x2 >= 1 ;\n",
        "+1 x1 +1 x2 <= 1 ;\n",
        "+1 x3 +1 x4 >= 1 ;\n",
        "+1 x3 +1 x4 <= 1 ;\n",
        "+1 x1 +1 x4 <= 1 ;\n",
        "+1 x1 +1 x3 <= 1 ;\n",
    );
    let input_path = write_temp_opb("cli-native-golomb-opt", opb);
    let proof_path = unique_temp_path("cli-native-golomb-opt", "pbp");
    let proof_arg = proof_path
        .to_str()
        .expect("temporary proof path should be utf-8");

    let (status, stdout, stderr) = run_standalone_ay_pb(
        &["--native", "--timeout", "5000", "--proof", proof_arg],
        &input_path,
    );

    assert_eq!(
        status.code(),
        Some(30),
        "standalone native Golomb OPT proof request should exit OPTIMUM FOUND; stdout: {stdout}; stderr: {stderr}"
    );
    assert!(
        stdout.lines().any(|line| line == "o 3"),
        "standalone native Golomb OPT proof request should emit objective 3: {stdout}"
    );
    assert!(
        stdout.contains("s OPTIMUM FOUND\n"),
        "standalone native Golomb OPT proof request should report OPTIMUM FOUND: {stdout}"
    );
    let proof = fs::read_to_string(&proof_path).expect("proof file should be readable");
    assert_feasible_opt_proof_contract(
        "standalone_cli_native_golomb_opt",
        opb,
        &proof,
        "conclusion BOUNDS 3 3;",
        None,
    );

    let _ = fs::remove_file(&input_path);
    let _ = fs::remove_file(&proof_path);
}

/// WBO-CERT (commit f42f5988) replaced the earlier fail-closed WBO proof refusal:
/// the CLI now projects WBO -> PBO, commits the projected formula to `<proof>.opb`,
/// and certifies the optimum against it. A pre-existing stale proof sidecar must
/// never survive: it is either replaced by the freshly certified proof (this case)
/// or removed on any fail-closed path.
#[test]
fn test_standalone_cli_wbo_proof_certifies_projection_and_replaces_stale_sidecar() {
    let wbo = "soft: 10 ;\n+1 x1 +1 x2 <= 1 ;\n+1 x1 +1 x2 >= 1 ;\n[4] +1 x1 <= 0 ;\n";
    let input_path = unique_temp_path("cli-wbo-proof", "wbo");
    fs::write(&input_path, wbo).expect("write temporary WBO input");
    let proof_path = unique_temp_path("cli-wbo-proof", "pbp");
    let formula_path = proof_path.with_extension("opb");
    fs::write(&proof_path, "stale WBO proof sidecar\n").expect("write stale proof sidecar");
    let proof_arg = proof_path
        .to_str()
        .expect("temporary proof path should be utf-8");

    let (status, stdout, stderr) =
        run_standalone_ay_pb(&["--timeout", "5000", "--proof", proof_arg], &input_path);

    assert_eq!(
        status.code(),
        Some(30),
        "standalone WBO proof request should exit OPTIMUM FOUND; stdout: {stdout}; stderr: {stderr}"
    );
    assert!(
        stdout.contains("WBO certified via PBO projection"),
        "standalone WBO proof request should announce the PBO projection: {stdout}"
    );
    // Optimum 0: x1=0, x2=1 satisfies both hard rows and the soft `[4] +1 x1 <= 0`.
    assert!(
        stdout.lines().any(|line| line == "o 0"),
        "standalone WBO proof request should emit objective 0: {stdout}"
    );
    assert!(
        stdout.contains("s OPTIMUM FOUND\n"),
        "standalone WBO proof request should report OPTIMUM FOUND: {stdout}"
    );
    let proof = fs::read_to_string(&proof_path).expect("proof file should be readable");
    assert!(
        !proof.contains("stale WBO proof sidecar"),
        "stale proof sidecar bytes must not survive a WBO proof request: {proof}"
    );
    assert!(
        proof.starts_with("pseudo-Boolean proof version 3.0\n"),
        "committed WBO-CERT proof must be a VeriPB v3 proof: {proof}"
    );
    let formula = fs::read_to_string(&formula_path)
        .expect("projected companion OPB formula should be committed");
    assert_feasible_opt_proof_contract(
        "standalone_cli_wbo_projection",
        &formula,
        &proof,
        "conclusion BOUNDS 0 0;",
        None,
    );

    let _ = fs::remove_file(&input_path);
    let _ = fs::remove_file(&proof_path);
    // WBO-CERT writes its companion (projected) OPB next to the PROOF path.
    let _ = fs::remove_file(&formula_path);
}

#[test]
fn test_equality_proof_header_counts_veripb_expanded_formula_rows() {
    let opb = "* #variable= 1 #constraint= 2 #equal= 1\n+1 x1 = 0 ;\n+1 x1 >= 1 ;\n";
    let instance = parse_opb(opb).expect("inline equality UNSAT instance must parse");
    let buf = SharedBytes::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");

    let result = solver.solve();
    assert_eq!(result, PbCdclResult::Unsatisfiable);
    solver
        .conclude_proof()
        .expect("UNSAT proof logging must still conclude successfully");

    let proof = buf.as_string();
    assert_eq!(
        proof.lines().nth(1),
        Some("f 3 ;"),
        "VeriPB expands one OPB equality row into two formula constraints: {proof}"
    );

    verify_with_local_veripb("equality_formula_rows", opb, &proof);
}

#[test]
fn test_equality_proof_ids_align_after_expanded_input_rows() {
    let opb = "\
* #variable= 6 #constraint= 6 #equal= 1\n\
+1 x1 +1 ~x1 = 1 ;\n\
+1 x1 +1 x2 >= 1 ;\n\
+1 x3 +1 x4 >= 1 ;\n\
+1 x5 +1 x6 >= 1 ;\n\
+1 ~x1 +1 ~x3 +1 ~x5 >= 2 ;\n\
+1 ~x2 +1 ~x4 +1 ~x6 >= 2 ;\n";
    let instance = parse_opb(opb).expect("inline equality-prefixed UNSAT instance must parse");
    let buf = SharedBytes::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");

    let result = solver.solve();
    assert_eq!(result, PbCdclResult::Unsatisfiable);
    solver
        .conclude_proof()
        .expect("UNSAT proof logging must still conclude successfully");

    let proof = buf.as_string();
    assert_eq!(
        proof.lines().nth(1),
        Some("f 7 ;"),
        "VeriPB expands the leading equality before later input row IDs: {proof}"
    );

    verify_with_local_veripb("equality_post_row_ids", opb, &proof);
}

#[test]
fn test_equality_proof_ids_skip_trivial_expanded_rows() {
    let opb = "\
* #variable= 7 #constraint= 6 #equal= 1\n\
+1 x7 = 0 ;\n\
+1 x1 +1 x2 >= 1 ;\n\
+1 x3 +1 x4 >= 1 ;\n\
+1 x5 +1 x6 >= 1 ;\n\
+1 ~x1 +1 ~x3 +1 ~x5 >= 2 ;\n\
+1 ~x2 +1 ~x4 +1 ~x6 >= 2 ;\n";
    let instance = parse_opb(opb)
        .expect("inline equality-prefixed UNSAT instance with skipped side must parse");
    let buf = SharedBytes::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");

    let result = solver.solve();
    assert_eq!(result, PbCdclResult::Unsatisfiable);
    solver
        .conclude_proof()
        .expect("UNSAT proof logging must still conclude successfully");

    let proof = buf.as_string();
    assert_eq!(
        proof.lines().nth(1),
        Some("f 7 ;"),
        "VeriPB still counts the skipped expanded equality side in the formula rows: {proof}"
    );

    verify_with_local_veripb("equality_skipped_expanded_row_ids", opb, &proof);
}

#[test]
fn test_le_source_unsat_proof_verifies_against_original_le_rows() {
    let opb = "\
* #variable= 1 #constraint= 2\n\
+1 x1 <= 0 ;\n\
+1 x1 >= 1 ;\n";
    assert!(
        opb.lines().any(|line| line.contains("<=")),
        "test OPB source must exercise an original <= row"
    );
    let instance = parse_opb(opb).expect("inline <= UNSAT instance must parse");
    let buf = SharedBytes::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");

    let result = solver.solve();
    assert_eq!(result, PbCdclResult::Unsatisfiable);
    solver
        .conclude_proof()
        .expect("<= UNSAT proof logging must conclude successfully");

    let proof = buf.as_string();
    assert_eq!(
        proof.lines().next(),
        Some("pseudo-Boolean proof version 3.0"),
        "<= UNSAT proof must use the VeriPB v3 header: {proof}"
    );
    assert_eq!(
        proof.lines().nth(1),
        Some("f 2 ;"),
        "each original <=/>= OPB row should import as one VeriPB formula row: {proof}"
    );
    assert!(
        proof.lines().any(|line| line == "rup >= 1 ;"),
        "<= UNSAT proof must derive contradiction as an empty-left-hand-side RUP step: {proof}"
    );
    assert!(
        proof.lines().any(|line| line == "output NONE;"),
        "<= UNSAT proof must include the VeriPB output marker: {proof}"
    );
    assert!(
        proof
            .lines()
            .any(|line| line.starts_with("conclusion UNSAT : ")),
        "<= UNSAT proof must conclude with a VeriPB UNSAT footer: {proof}"
    );
    assert!(
        !proof.lines().any(|line| line.starts_with("conclusion SAT")),
        "<= UNSAT proof must not claim SAT: {proof}"
    );
    assert!(
        proof.lines().last() == Some("end pseudo-Boolean proof;"),
        "<= UNSAT proof must end with the VeriPB proof terminator: {proof}"
    );

    verify_with_local_veripb("le_source_unsat", opb, &proof);
}

#[test]
fn test_unsat_proof_header_uses_original_constraint_count_after_preprocess_unsat() {
    let instance = parse_opb("* #variable= 1 #constraint= 2\n+1 x1 >= 1 ;\n+1 ~x1 >= 1 ;\n")
        .expect("inline contradictory PB instance must parse");
    let buf = SharedBytes::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");

    let result = solver.solve();
    assert_eq!(result, PbCdclResult::Unsatisfiable);
    solver
        .conclude_proof()
        .expect("UNSAT proof logging must still conclude successfully");

    let proof = buf.as_string();
    assert_eq!(
        proof.lines().nth(1),
        Some("f 2 ;"),
        "proof header must report the original OPB constraint count even if preprocessing collapses the working formula: {proof}"
    );
    assert!(
        proof.lines().any(|line| line.starts_with("rup ")),
        "collapsed UNSAT proof must still derive contradiction via a RUP step: {proof}"
    );
    assert!(
        proof.lines().any(|line| line == "output NONE;"),
        "collapsed UNSAT proof must include the VeriPB output marker: {proof}"
    );
    assert!(
        proof
            .lines()
            .any(|line| line.starts_with("conclusion UNSAT : ")),
        "collapsed UNSAT proof must conclude with a VeriPB UNSAT footer: {proof}"
    );
    assert!(
        proof.lines().last() == Some("end pseudo-Boolean proof;"),
        "collapsed UNSAT proof must end with the VeriPB proof terminator: {proof}"
    );
    assert!(
        !proof.lines().any(|line| line.starts_with("c ")),
        "collapsed UNSAT proof must not depend on the legacy checker-local c marker: {proof}"
    );
}

#[test]
fn test_optimization_proof_logging_emits_opt_conclusion() {
    let opb = load_instance_source("weighted_opt.opb");
    let instance =
        parse_opb(&opb).unwrap_or_else(|e| panic!("failed to parse weighted_opt.opb: {e}"));
    let objective = instance
        .objective
        .as_ref()
        .expect("weighted_opt.opb must contain an objective");
    let buf = SharedBytes::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");

    let result = solver.solve_optimize(objective, None);
    assert!(
        matches!(result, PbCdclResult::Optimal(_, _)),
        "weighted_opt.opb should solve to an optimal result, got {result:?}"
    );
    solver
        .conclude_proof()
        .expect("completed optimization proof logging must conclude successfully");

    let proof = buf.as_string();
    assert_feasible_opt_proof_contract(
        "weighted_opt",
        &opb,
        &proof,
        "conclusion BOUNDS 5 5;",
        None,
    );
}

#[test]
fn test_tiny_optimization_proof_logging_uses_veripb_solution_improvement() {
    let opb = "* #variable= 1 #constraint= 1\nmin: +1 x1 ;\n+1 x1 >= 1 ;\n";
    let instance = parse_opb(opb).expect("tiny optimization canary must parse");
    let objective = instance
        .objective
        .as_ref()
        .expect("tiny optimization canary must contain an objective");
    let buf = SharedBytes::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");

    let result = solver.solve_optimize(objective, None);
    assert!(
        matches!(result, PbCdclResult::Optimal(_, 1)),
        "tiny optimization canary should solve to optimum 1, got {result:?}"
    );
    solver
        .conclude_proof()
        .expect("completed optimization proof logging must conclude successfully");

    let proof = buf.as_string();
    assert_feasible_opt_proof_contract(
        "tiny_opt",
        opb,
        &proof,
        "conclusion BOUNDS 1 1;",
        Some("soli x1;"),
    );
}

#[test]
fn test_infeasible_optimization_proof_logging_verifies_inf_bounds() {
    let opb = "* #variable= 1 #constraint= 2\nmin: +1 x1 ;\n+1 x1 >= 1 ;\n+1 ~x1 >= 1 ;\n";
    let instance = parse_opb(opb).expect("infeasible optimization canary must parse");
    let objective = instance
        .objective
        .as_ref()
        .expect("infeasible optimization canary must contain an objective");
    let buf = SharedBytes::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");

    let result = solver.solve_optimize(objective, None);
    assert_eq!(
        result,
        PbCdclResult::Unsatisfiable,
        "infeasible optimization canary should have no feasible incumbent"
    );
    solver
        .conclude_proof()
        .expect("infeasible optimization proof logging must conclude successfully");

    let proof = buf.as_string();
    assert_opt_bounds_proof_contract("infeasible_opt", opb, &proof, "conclusion BOUNDS INF INF;");
    assert!(
        !proof.lines().any(|line| line.starts_with("soli ")),
        "infeasible OPT proof must not log an incumbent: {proof}"
    );
}

#[test]
fn test_equality_optimization_proof_logging_verifies_expanded_rows() {
    let opb = "\
* #variable= 2 #constraint= 2 #equal= 1\n\
min: +1 x1 +2 x2 ;\n\
+1 x1 = 1 ;\n\
+1 x2 >= 1 ;\n";
    let instance = parse_opb(opb).expect("equality optimization canary must parse");
    let objective = instance
        .objective
        .as_ref()
        .expect("equality optimization canary must contain an objective");
    let buf = SharedBytes::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");

    let result = solver.solve_optimize(objective, None);
    assert!(
        matches!(result, PbCdclResult::Optimal(_, 3)),
        "equality optimization canary should solve to optimum 3, got {result:?}"
    );
    solver
        .conclude_proof()
        .expect("equality optimization proof logging must conclude successfully");

    let proof = buf.as_string();
    assert_eq!(
        proof.lines().nth(1),
        Some("f 3 ;"),
        "VeriPB expands the equality OPT row in the proof header: {proof}"
    );
    assert_feasible_opt_proof_contract(
        "equality_opt",
        opb,
        &proof,
        "conclusion BOUNDS 3 3;",
        Some("soli x1 x2;"),
    );
}

#[test]
fn test_le_source_optimization_proof_verifies_against_original_le_rows() {
    // `+1 x1 <= 0` forces x1=0, then `x1+x2>=1` forces x2=1, so min x1+2x2 = 2.
    // The objective floor `x1 + 2 x2 >= 2` requires `2*(x1+x2>=1) + 1*(-x1>=0)`:
    // a positive combination that CANCELS a coefficient overshoot on x1 against
    // the `<=` row. The native structural cut builder cannot express that
    // cancellation, so the native OPT proof must FAIL CLOSED
    // (opt_lower_bound_deferred) rather than emit an unverifiable `rup >= 1 ;`
    // that has no supporting propagation in the (learned-clause-suppressed)
    // proof database. The certified OPT-LIN fallback then closes the bound from a
    // real augmented-instance refutation, and THAT proof verifies against the
    // original <= rows.
    let opb = "\
* #variable= 2 #constraint= 2\n\
min: +1 x1 +2 x2 ;\n\
+1 x1 <= 0 ;\n\
+1 x1 +1 x2 >= 1 ;\n";
    assert!(
        opb.lines().any(|line| line.contains("<=")),
        "test OPB source must exercise an original <= row"
    );
    let instance = parse_opb(opb).expect("inline <= optimization instance must parse");
    let objective = instance
        .objective
        .as_ref()
        .expect("inline <= optimization instance must contain an objective");
    let buf = SharedBytes::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");

    let result = solver.solve_optimize(objective, None);
    let PbCdclResult::Optimal(incumbent, 2) = result else {
        panic!("<= optimization canary should solve to optimum 2, got {result:?}");
    };

    // Native path FAILS CLOSED: it must not ship an unverifiable `rup >= 1 ;`.
    assert!(
        solver.opt_lower_bound_deferred(),
        "<= OPT native lower bound (needs an overshoot-cancelling cut) must defer"
    );
    let err = solver.conclude_proof().expect_err(
        "native <= OPT proof must fail closed when the structural cut is inexpressible",
    );
    assert!(
        matches!(err, ProofError::UnprovableOptimizationLowerBound),
        "native defer must surface as UnprovableOptimizationLowerBound, got {err:?}"
    );
    let native_proof = buf.as_string();
    assert!(
        !native_proof.lines().any(|line| line == "rup >= 1 ;"),
        "failed-closed native proof must NOT emit an unsupported `rup >= 1 ;`: {native_proof}"
    );
    assert!(
        !native_proof
            .lines()
            .any(|line| line.starts_with("conclusion BOUNDS")),
        "failed-closed native proof must NOT claim OPT bounds: {native_proof}"
    );

    // The certified OPT-LIN fallback closes the SAME <= instance from a real
    // refutation; this is the proof the CLI commits on the deferral path.
    let proof = certify_opt_lin_bounds(&instance, &incumbent, 2)
        .expect("OPT-LIN-CERT fallback must certify the <= instance optimum");
    assert_eq!(
        proof.lines().next(),
        Some("pseudo-Boolean proof version 3.0"),
        "<= OPT proof must use the VeriPB v3 header: {proof}"
    );
    assert_eq!(
        proof.lines().nth(1),
        Some("f 2 ;"),
        "each original <=/>= OPB row should import as one VeriPB formula row: {proof}"
    );
    assert_feasible_opt_proof_contract(
        "le_source_opt",
        opb,
        &proof,
        "conclusion BOUNDS 2 2;",
        Some("soli ~x1 x2;"),
    );
}

#[test]
fn test_interrupted_optimization_proof_logging_fails_closed() {
    let instance = exactly_one_instance(32);
    let objective = instance
        .objective
        .as_ref()
        .expect("optimization instance must carry an objective");
    let buf = SharedBytes::new();
    let mut solver = PbCdclSolver::with_proof_writer(&instance, buf.clone())
        .expect("proof writer creation must succeed");
    let should_stop = Cell::new(false);
    let mut on_improve = |_: i128, _: &[bool]| should_stop.set(true);

    let result =
        solver.solve_optimize_interruptible(objective, Some(&mut on_improve), || should_stop.get());
    assert!(
        matches!(result, PbCdclResult::Feasible(_, _)),
        "interrupt after the first incumbent should keep only a feasible result, got {result:?}"
    );

    let err = solver
        .conclude_proof()
        .expect_err("incomplete optimization proof logging must still fail closed");
    assert!(matches!(err, ProofError::MissingOptimizationBounds));

    let proof = buf.as_string();
    assert!(
        !proof.lines().any(|line| line == "output NONE;"),
        "interrupted optimization proof must not claim a final proof result: {proof}"
    );
    assert!(
        !proof
            .lines()
            .any(|line| line.starts_with("conclusion BOUNDS ")),
        "interrupted optimization proof must not claim final OPT bounds: {proof}"
    );
    assert!(
        !proof.contains("conclusion UNSAT"),
        "interrupted optimization proof must not claim UNSAT: {proof}"
    );
}

#[test]
fn test_opt_lin_cert_soli_plus_certified_unsat_lower_bound_verifies_bounds() {
    // OPT-LIN-CERT lever: prove the optimum of `min x1+x2+x3` subject to
    // "exactly two of three true" is V=2, assembling the certificate as
    //   soli(incumbent achieving 2)  +  certified-UNSAT refutation of {instance ∧ obj<=1}.
    // The constraints force the sum to exactly 2 (>= 2 AND <= 2), so the unique
    // objective value is 2; any "strictly better" (obj <= 1) is infeasible.
    let opb = concat!(
        "* #variable= 3 #constraint= 2\n",
        "min: +1 x1 +1 x2 +1 x3 ;\n",
        "+1 x1 +1 x2 +1 x3 >= 2 ;\n",
        "-1 x1 -1 x2 -1 x3 >= -2 ;\n",
    );
    let instance = parse_opb(opb).expect("OPT-LIN-CERT canary must parse");

    // Hand-confirmed optimum and a feasible incumbent achieving it.
    let optimum: i128 = 2;
    let incumbent = vec![true, true, false]; // x1=1 x2=1 x3=0 -> obj = 2

    let proof = certify_opt_lin_bounds(&instance, &incumbent, optimum)
        .expect("OPT-LIN-CERT helper must produce a proof for the optimal incumbent");

    // Structural contract: a soli row for the upper bound, a refutation closing the
    // lower bound, and a single OPT BOUNDS conclusion (never a decision conclusion).
    assert!(
        proof.lines().any(|line| line.starts_with("soli ")),
        "OPT-LIN-CERT proof must log the incumbent via soli: {proof}"
    );
    assert!(
        proof.lines().any(|line| line.starts_with("rup ")),
        "OPT-LIN-CERT proof must close the lower bound via lifted rup steps: {proof}"
    );
    assert_feasible_opt_proof_contract(
        "opt_lin_cert_soli_plus_unsat",
        opb,
        &proof,
        "conclusion BOUNDS 2 2;",
        Some("soli x1 x2 ~x3;"),
    );
}

#[test]
fn test_opt_lin_cert_compact_soli_plus_certified_unsat_lower_bound_verifies_bounds() {
    // OPT-LIN-CERT, COMPACT lower bound: prove the optimum of
    // `min x1+x2+x3+x4` subject to "exactly three of four true" is V=3,
    // assembling the certificate as
    //   soli(incumbent achieving 3)
    //   + COMPACT certified-UNSAT refutation of {instance ∧ obj<=2}.
    // The augmented refutation needs Sinz aux registers: the `>= 3` row AND the
    // soli-installed objective-improving row `obj<=2` (normalized rhs 2) are both
    // threshold >= 2, so the compact encoder Sinz-encodes them. This is exactly the
    // class the aux-free opt-cert declines — it exercises the compact path.
    let opb = concat!(
        "* #variable= 3 #constraint= 2\n",
        "min: +1 x1 +1 x2 +1 x3 ;\n",
        "+1 x1 >= 1 ;\n",
        "+1 x2 >= 1 ;\n",
    );
    let instance = parse_opb(opb).expect("OPT-LIN-CERT compact canary must parse");

    // Hand-confirmed optimum and a feasible incumbent achieving it: x1,x2 forced
    // true by the units, x3 free; the minimum objective value is 2 (x3 = 0).
    let optimum: i128 = 2;
    let incumbent = vec![true, true, false]; // obj = 2

    let proof = certify_opt_lin_bounds_compact(&instance, &incumbent, optimum)
        .expect("compact OPT-LIN-CERT helper must produce a proof for the optimal incumbent");

    // Structural contract: a soli row for the upper bound, `red` Sinz definition
    // introductions + `pol` top-register telescope for the lower bound, lifted
    // `rup` steps, and a single OPT BOUNDS conclusion (never a decision conclusion).
    assert!(
        proof.lines().any(|line| line.starts_with("soli ")),
        "compact OPT-LIN-CERT proof must log the incumbent via soli: {proof}"
    );
    assert!(
        proof.lines().any(|line| line.starts_with("red ")),
        "compact OPT-LIN-CERT proof must `red`-introduce Sinz definitions: {proof}"
    );
    assert!(
        proof.lines().any(|line| line.starts_with("pol ")),
        "compact OPT-LIN-CERT proof must derive top registers via pol: {proof}"
    );
    assert!(
        proof.lines().any(|line| line.starts_with("rup ")),
        "compact OPT-LIN-CERT proof must close the lower bound via lifted rup steps: {proof}"
    );
    assert_feasible_opt_proof_contract(
        "opt_lin_cert_compact_soli_plus_unsat",
        opb,
        &proof,
        "conclusion BOUNDS 2 2;",
        Some("soli x1 x2 ~x3;"),
    );
}

#[test]
fn test_opt_lin_cert_compact_withholds_certificate_for_non_optimal_incumbent() {
    // A feasible incumbent that is NOT optimal must NOT yield a BOUNDS proof from
    // the compact path either: the augmented refutation {instance ∧ obj<=optimum-1}
    // would be SAT (a better solution exists), so the helper declines (fail-closed,
    // status unaffected). Here we falsely claim optimum=4 with a value-4 incumbent;
    // obj<=3 is feasible (three-true models exist).
    let opb = concat!(
        "* #variable= 4 #constraint= 1\n",
        "min: +1 x1 +1 x2 +1 x3 +1 x4 ;\n",
        "+1 x1 +1 x2 +1 x3 +1 x4 >= 3 ;\n",
    );
    let instance = parse_opb(opb).expect("non-optimal compact canary must parse");
    let incumbent = vec![true, true, true, true]; // obj = 4, feasible but not optimal

    let proof = certify_opt_lin_bounds_compact(&instance, &incumbent, 4);
    assert!(
        proof.is_none(),
        "compact OPT-LIN-CERT helper must withhold a certificate when the incumbent is not optimal: {proof:?}"
    );
}

#[test]
fn test_opt_lin_cert_withholds_certificate_for_non_optimal_incumbent() {
    // A feasible incumbent that is NOT optimal must NOT yield a BOUNDS proof: the
    // augmented refutation {instance ∧ obj<=optimum-1} would be SAT (a better
    // solution exists), so the helper declines (fail-closed, status unaffected).
    // Here we falsely claim optimum=3 with a value-3 incumbent; obj<=2 is feasible
    // (two-true models exist), so no lower bound at 3 can be certified.
    let opb = concat!(
        "* #variable= 3 #constraint= 1\n",
        "min: +1 x1 +1 x2 +1 x3 ;\n",
        "+1 x1 +1 x2 +1 x3 >= 2 ;\n",
    );
    let instance = parse_opb(opb).expect("non-optimal canary must parse");
    let incumbent = vec![true, true, true]; // obj = 3, feasible but not optimal

    let proof = certify_opt_lin_bounds(&instance, &incumbent, 3);
    assert!(
        proof.is_none(),
        "OPT-LIN-CERT helper must withhold a certificate when the incumbent is not optimal: {proof:?}"
    );
}

#[test]
fn test_opt_lin_cert_pb_native_certifies_aux_heavy_big_coefficient_optimum() {
    // OPT-LIN-CERT, PB-NATIVE lower bound: the aux-heavy class BOTH CNF routes
    // decline (2026-07-15 round-3 audit repro `auxlift-gap-t2.opb`). The ~2^47
    // coefficients make the compact route's Sinz aux count (`lits * rhs`) blow
    // its budget, and the aux-free route's adder/BDD DRAT references encoding
    // aux variables, so before the PB-native route the pipeline forfeited this
    // OPTIMUM to a bare SATISFIABLE. The PB-native refutation of
    // {instance ∧ obj <= 2} introduces no aux variables at all.
    let opb = concat!(
        "* #variable= 6 #constraint= 4\n",
        "min: +1 x1 +1 x3 +1 x4 +1 x5 +1 x6 ;\n",
        "+6707464769161 x1 +79319458732615 x2 +139107397615471 x3 ",
        "+57256190630981 x4 +17850223300992 x5 +125506394628793 x6 ",
        ">= 214485218460026 ;\n",
        "+65835948102843 x1 +7226099990789 x4 +37220036638851 x5 ",
        "+18543202694047 x6 >= 69190988522800 ;\n",
        "+111154655673075 x2 +31938719893265 x3 +120025655342763 x4 ",
        "+4342502136085 x5 +42597450852618 x6 >= 80606946172027 ;\n",
        "+81341586348879 x1 +75427986547918 x3 +35464878525533 x4 ",
        "+32788823422758 x6 >= 44935608338545 ;\n",
    );
    let instance = parse_opb(opb).expect("aux-heavy PB-native canary must parse");

    // Hand-confirmed optimum and a feasible incumbent achieving it (the
    // solver's own verdict on the repro): x1,x2,x5,x6 true -> obj = 3.
    let optimum: i128 = 3;
    let incumbent = vec![true, true, false, false, true, true];

    let proof = certify_opt_lin_bounds_pb(&instance, &incumbent, optimum)
        .expect("PB-native OPT-LIN-CERT helper must certify the aux-heavy optimum");

    // Structural contract: a soli row for the upper bound, a checked
    // cutting-planes (`pol`) refutation closing the lower bound, and a single
    // hinted OPT BOUNDS conclusion (never a decision conclusion).
    assert!(
        proof.lines().any(|line| line.starts_with("pol ")),
        "PB-native OPT-LIN-CERT proof must close the lower bound via pol steps: {proof}"
    );
    assert_feasible_opt_proof_contract(
        "opt_lin_cert_pb_native_aux_heavy",
        opb,
        &proof,
        "conclusion BOUNDS 3 3;",
        Some("soli x1 x2 ~x3 ~x4 x5 x6;"),
    );
    // Both deletion modes: `-u` discounts soli-logged solutions, so this also
    // pins that the conclusion carries its contradiction-row + witness hints.
    verify_with_local_veripb_unchecked_deletions("opt_lin_cert_pb_native_aux_heavy", opb, &proof);
}

#[test]
fn test_opt_lin_cert_pb_native_handles_equality_rows_and_negated_objective_literals() {
    // PB-NATIVE route id-alignment canary: an EQUALITY row consumes TWO VeriPB
    // input ids (the `>=` and `<=`-as-`>=` directions), so the soli-installed
    // objective-improving row must land at id f_count+1 = 4 for the solver's
    // imported-input map to stay in lockstep with the checker. The negated
    // objective literal (`~x1`) additionally pins the soli/objective semantics
    // the improving row mirrors.
    let opb = concat!(
        "* #variable= 3 #constraint= 2\n",
        "min: +2 ~x1 +1 x2 +1 x3 ;\n",
        "+1 x1 +1 x2 = 1 ;\n",
        "+1 x2 +1 x3 >= 1 ;\n",
    );
    let instance = parse_opb(opb).expect("equality/negated-literal canary must parse");

    // Hand-confirmed optimum: the equality forces exactly one of {x1,x2}.
    // x1=1,x2=0 needs x3=1 (second row), obj = 1; x1=0,x2=1 costs obj >= 3.
    let optimum: i128 = 1;
    let incumbent = vec![true, false, true]; // obj = 0 + 0 + 1 = 1

    let proof = certify_opt_lin_bounds_pb(&instance, &incumbent, optimum)
        .expect("PB-native OPT-LIN-CERT helper must certify across an equality row");

    assert_feasible_opt_proof_contract(
        "opt_lin_cert_pb_native_equality",
        opb,
        &proof,
        "conclusion BOUNDS 1 1;",
        Some("soli x1 ~x2 x3;"),
    );
    verify_with_local_veripb_unchecked_deletions("opt_lin_cert_pb_native_equality", opb, &proof);
}

#[test]
fn test_opt_lin_cert_pb_native_withholds_certificate_for_non_optimal_incumbent() {
    // A feasible incumbent that is NOT optimal must NOT yield a BOUNDS proof
    // from the PB-native path either: the augmented {instance ∧ obj<=optimum-1}
    // is SAT (a better solution exists), so the helper declines (fail-closed,
    // status unaffected).
    let opb = concat!(
        "* #variable= 3 #constraint= 1\n",
        "min: +1 x1 +1 x2 +1 x3 ;\n",
        "+1 x1 +1 x2 +1 x3 >= 2 ;\n",
    );
    let instance = parse_opb(opb).expect("non-optimal PB-native canary must parse");
    let incumbent = vec![true, true, true]; // obj = 3, feasible but not optimal

    let proof = certify_opt_lin_bounds_pb(&instance, &incumbent, 3);
    assert!(
        proof.is_none(),
        "PB-native OPT-LIN-CERT helper must withhold a certificate when the incumbent is not optimal: {proof:?}"
    );
}
