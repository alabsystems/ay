// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use sha2::{Digest, Sha256};
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::Duration;
use wait_timeout::ChildExt;

fn run(binary: &Path, args: &[&std::ffi::OsStr], dir: &Path, tag: &str) -> (bool, String) {
    let out = dir.join(format!("{tag}.out"));
    let err = dir.join(format!("{tag}.err"));
    let mut child = Command::new(binary)
        .args(args)
        .stdin(Stdio::null())
        .stdout(std::fs::File::create(&out).unwrap())
        .stderr(std::fs::File::create(&err).unwrap())
        .spawn()
        .unwrap();
    let Some(status) = child.wait_timeout(Duration::from_secs(5)).unwrap() else {
        child.kill().unwrap();
        child.wait().unwrap();
        panic!("pinned checker exceeded its five-second test envelope");
    };
    assert!(std::fs::metadata(&out).unwrap().len() < 1024 * 1024);
    assert!(std::fs::metadata(&err).unwrap().len() < 1024 * 1024);
    (
        status.success(),
        format!(
            "{}\n{}",
            std::fs::read_to_string(out).unwrap(),
            std::fs::read_to_string(err).unwrap()
        ),
    )
}

#[test]
fn native_universal_lineage_whole_pinned_carcara_and_forged_instance() {
    let (mut exec, root) = fixture();
    let receipt = source(&exec);
    let falsity = exec.ctx.terms.false_term();
    let exact = exec
        .native_universal_instance(&receipt, root, &[falsity])
        .unwrap();
    let mut proof = Proof::new();
    let unit = exec.emit_native_forall_unit(&mut proof, root, &[falsity], exact);
    let not_false = exec.ctx.terms.mk_not_raw(falsity);
    let axiom = proof.add_rule_step(AletheRule::False, vec![not_false], Vec::new(), Vec::new());
    proof.add_resolution(Vec::new(), falsity, unit, axiom);
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &exec.ctx.terms,
        receipt.roots(),
        None,
    )
    .unwrap();
    // The canonical assertion is rendered from the same exact source TermId;
    // this fixture has no free symbols, sort declarations, or source aliases.
    let problem = format!(
        "(set-logic ALL)\n(assert {})\n(check-sat)\n",
        ay_proof::format_term_alethe(&exec.ctx.terms, root)
    );
    ay_core::pinned_carcara::pinned_carcara_can_judge(&problem, &document).unwrap();
    let binary = std::env::split_paths(&std::env::var_os("PATH").unwrap())
        .map(|p| p.join("carcara"))
        .find(|p| p.is_file())
        .unwrap()
        .canonicalize()
        .unwrap();
    let before = Sha256::digest(std::fs::read(&binary).unwrap());
    let dir = tempfile::tempdir().unwrap();
    let (ok, version) = run(
        &binary,
        &[std::ffi::OsStr::new("--version")],
        dir.path(),
        "version",
    );
    assert!(
        ok && version.contains("carcara 1.1.0") && version.contains("9a352ee"),
        "{version}"
    );
    let smt = dir.path().join("source.smt2");
    let alethe = dir.path().join("proof.alethe");
    std::fs::write(&smt, &problem).unwrap();
    std::fs::write(&alethe, &document).unwrap();
    let args = [
        std::ffi::OsStr::new("check"),
        std::ffi::OsStr::new("--"),
        alethe.as_os_str(),
        smt.as_os_str(),
    ];
    let (ok, output) = run(&binary, &args, dir.path(), "positive");
    assert!(
        ok && output.lines().any(|line| line == "valid"),
        "{output}\n{document}"
    );
    let mut forged = proof.clone();
    let inst = forged
        .steps
        .iter_mut()
        .find_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::ForallInst,
                args,
                ..
            } => Some(args),
            _ => None,
        })
        .unwrap();
    inst[0] = exec.ctx.terms.true_term();
    assert!(
        exec.check_proof_strict_with_datatypes(&forged).is_err(),
        "wrong typed instance must fail independently"
    );
    // Keep the whole real document and its false conclusion; replace only the
    // final rule with refl, which cannot derive the empty clause. This tests
    // semantic rejection rather than an unsupported grammar/parse failure.
    let mut forged_document = document.clone();
    let start = forged_document.rfind(":rule ").unwrap() + ":rule ".len();
    let end = forged_document[start..]
        .find(|c: char| c.is_ascii_whitespace() || c == ')')
        .map_or(forged_document.len(), |n| start + n);
    assert!(forged_document[..start].rfind("(cl)").is_some());
    forged_document.replace_range(start..end, "refl");
    ay_core::pinned_carcara::pinned_carcara_can_judge(&problem, &forged_document).unwrap();
    std::fs::write(&alethe, &forged_document).unwrap();
    let (ok, output) = run(&binary, &args, dir.path(), "forged");
    assert!(
        !ok && output.lines().any(|line| line == "invalid"),
        "{output}"
    );
    assert_eq!(before, Sha256::digest(std::fs::read(&binary).unwrap()));
    eprintln!("native universal whole pinned checker: binary={before:x} problem={:x} proof={:x}; forged final refl rejected", Sha256::digest(problem.as_bytes()), Sha256::digest(document.as_bytes()));
}
